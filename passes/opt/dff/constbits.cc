/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *  Copyright (C) 2020  Marcelina Kościelnicka <mwk@0x04.net>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/ff.h"
#include "passes/opt/dff/opt_dff.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ConstBitsContext
{
	OptDffWorker &worker;

	// opt_dff -sat rebuilds the solver in batches of at most this many imported
	// cells, so one pathological module can't grow a single giant solver
	int sat_batch_cells;

	ConstBitsContext(OptDffWorker &worker) : worker(worker),
		sat_batch_cells(worker.module->design->scratchpad_get_int("opt_dff.sat_batch_cells", 10000)) { }

	// lattice join of candidate constants: Sx is the identity (unless -keepdc
	// pins it), equal values join, Sm marks a conflict
	State combine_const(State a, State b) {
		if (a == State::Sx && !worker.opt.keepdc) return b;
		if (b == State::Sx && !worker.opt.keepdc) return a;
		if (a == b) return a;
		return State::Sm;
	}

	// candidate stuck-at value of ff bit i, joined over every non-D way the bit
	// can acquire a value: init, arst, srst and sr (a clr/set that can ever
	// fire forces 0/1)
	// returns S0/S1 as the candidate, Sx if unconstrained, Sm on conflict
	// the candidate doubles as the induction base case
	State check_constbit(FfData &ff, int i)
	{
		State val = ff.val_init[i];
		if (ff.has_arst) val = combine_const(val, ff.val_arst[i]);
		if (ff.has_srst) val = combine_const(val, ff.val_srst[i]);
		if (ff.has_sr) {
			if (!worker.is_inactive(worker.sigmap(ff.sig_clr[i]), ff.pol_clr))
				val = combine_const(val, State::S0);
			if (!worker.is_inactive(worker.sigmap(ff.sig_set[i]), ff.pol_set))
				val = combine_const(val, State::S1);
		}

		return val;
	}

	// an input that must be shown to feed the candidate value back into the bit
	// whenever it loads: D only while ce is active and srst is not, AD always
	struct ConstTarget {
		SigBit sig;
		SigBit ce = State::S1, srst = State::S0;
		bool pol_ce = true, pol_srst = true;
		bool gated = false;          // ce or srst can keep sig from loading
	};

	// candidate constant of one ff bit, with every constant input already folded in
	struct ConstCandidate {
		State val = State::Sm;
		std::vector<ConstTarget> targets;

		bool needs_proof() const { return !targets.empty(); }
	};

	// one suspected-constant ff bit: q (output of cell at bit idx) looks stuck
	// at val, and sat must show that every target feeds val back into the bit
	struct ConstObligation {
		// Held: proven assuming every candidate still standing holds too, which
		// a later batch's drop can undo
		enum Status { Pending, Proven, Held, Dropped };

		Cell *cell;
		int idx;
		State val;
		SigBit q;
		std::vector<ConstTarget> targets;
		Status status = Pending;

		int q_lit = -1;              // valid within the current batch
		int differ_lit = -1;         // some target differs from the candidate value
		int act_lit = -1;            // differ_lit counts in a joint sweep's query while set
	};

	// the solver model captures (differ, q) of every pending obligation so one
	// counterexample can disprove many at once
	struct ConstWatchList {
		// interleaved pairs, exprs[2k] = differ_lit and exprs[2k + 1] = q_lit of obs[k]
		std::vector<int> exprs;
		std::vector<ConstObligation *> obs;

		void watch(ConstObligation &ob) {
			exprs.push_back(ob.differ_lit);
			exprs.push_back(ob.q_lit);
			obs.push_back(&ob);
		}

		// drop every obligation whose q holds its constant while some target
		// differs, and return the ones not dropped before
		std::vector<ConstObligation *> drop_disproven(const std::vector<bool> &model) const {
			std::vector<ConstObligation *> dropped;
			for (int k = 0; k < GetSize(obs); k++) {
				bool want = (obs[k]->val == State::S1);
				if (model[2*k + 1] == want && model[2*k] && obs[k]->status != ConstObligation::Dropped) {
					obs[k]->status = ConstObligation::Dropped;
					dropped.push_back(obs[k]);
				}
			}
			return dropped;
		}
	};

	void commit_const(dict<Cell *, pool<int>> &const_bits, Cell *cell, int idx, SigBit q, State val)
	{
		log("Setting constant %d-bit at position %d on %s (%s) from module %s.\n",
				val == State::S1 ? 1 : 0, idx, cell, cell->type.unescape(), worker.module);
		worker.initvals.remove_init(q);
		worker.module->connect(q, val);
		const_bits[cell].insert(idx);
	}

	// an input can only be proven against a definite candidate value, and an
	// undriven one only when ce or srst may keep it from ever loading
	bool add_const_target(ConstObligation &ob, const ConstTarget &target)
	{
		if (ob.val != State::S0 && ob.val != State::S1)
			return false;
		if (!target.gated && !worker.get_modwalker().has_drivers(target.sig))
			return false;
		ob.targets.push_back(target);
		return true;
	}

	// an undriven input that is neither its own ce nor srst, not on a onehot wire (whose
	// bits the solver ties together), and that no imported cell reads is outside the cone
	// of its load condition, so it can take any value there. Map through the walker, as
	// the solver does: it also sees bits committed constant
	bool free_input(QuickConeSat &qcsat, const ConstTarget &target)
	{
		SigMap &sigmap = qcsat.modwalker.sigmap;
		SigBit sig = sigmap(target.sig);
		if (!sig.wire || sig == sigmap(target.ce) || sig == sigmap(target.srst) ||
				sig.wire->get_bool_attribute(ID::onehot) || qcsat.modwalker.has_drivers(sig))
			return false;
		auto it = qcsat.modwalker.signal_consumers.find(sig);
		if (it != qcsat.modwalker.signal_consumers.end())
			for (auto &pbit : it->second)
				if (qcsat.imported_cells.count(pbit.cell))
					return false;
		return true;
	}

	// literal for sig being at level pol, constant for a constant sig
	int import_level(QuickConeSat &qcsat, SigBit sig, bool pol)
	{
		int lit = sig.wire ? qcsat.importSigBit(sig) : qcsat.ez->value(sig == State::S1);
		return pol ? lit : qcsat.ez->NOT(lit);
	}

	// try to decide obligation ob under the given per-query effort cap, returns
	// true if the cap was hit and the obligation had to be left pending
	bool resolve_const_obligation(QuickConeSat &qcsat, int64_t cap, ConstObligation &ob,
			const ConstWatchList &watches)
	{
		// induction step: assuming q already holds the candidate value, the values
		// fed through the targets must equal it again, since check_constbit provides the
		// base case, so unsat makes the constant an inductive invariant
		int vlit = qcsat.ez->value(ob.val == State::S1);
		std::vector<int> assumptions;
		assumptions.push_back(qcsat.ez->IFF(ob.q_lit, vlit));
		assumptions.push_back(ob.differ_lit);

		std::vector<bool> model;
		auto res = worker.sat_budget.solve(qcsat, cap, watches.exprs, model, assumptions);

		if (res == SatEffortBudget::Result::LimitReached)
			return true;
		if (res == SatEffortBudget::Result::Unsat) {
			ob.status = ConstObligation::Proven;
			return false;
		}

		watches.drop_disproven(model);
		ob.status = ConstObligation::Dropped;
		return false;
	}

	// fold every constant input into the candidate from check_constbit, so a
	// wire input that sigmaps to a constant counts as constant too. A constant D
	// that contradicts the candidate stays a target when ce or srst gate it, since
	// sat may show it never loads while q holds the candidate
	ConstCandidate fold_const_inputs(FfData &ff, int i)
	{
		ConstCandidate cand;

		State val = check_constbit(ff, i);
		if (val == State::Sm)
			return cand;

		bool has_d = ff.has_clk || ff.has_gclk;
		SigBit d = has_d ? worker.sigmap(ff.sig_d[i]) : SigBit();
		SigBit ad = ff.has_aload ? worker.sigmap(ff.sig_ad[i]) : SigBit();

		if (has_d) {
			ConstTarget target;
			target.sig = d;
			target.gated = ff.has_ce || ff.has_srst;
			if (ff.has_ce) {
				target.ce = worker.sigmap(ff.sig_ce[0]);
				target.pol_ce = ff.pol_ce;
			}
			if (ff.has_srst) {
				target.srst = worker.sigmap(ff.sig_srst[0]);
				target.pol_srst = ff.pol_srst;
			}
			if (d.wire || (target.gated && combine_const(val, d.data) == State::Sm))
				cand.targets.push_back(target);
			else
				val = combine_const(val, d.data);
		}
		if (ff.has_aload) {
			if (ad.wire)
				cand.targets.push_back({ad});
			else
				val = combine_const(val, ad.data);
		}

		cand.val = val;
		return cand;
	}

	// commit the bits that are constant by folding alone and return the ones
	// that still have a wire input
	std::vector<ConstObligation> fold_const_bits(dict<Cell *, pool<int>> &const_bits)
	{
		std::vector<ConstObligation> obligations;

		for (auto cell : worker.module->selected_cells()) {
			if (!cell->is_builtin_ff())
				continue;

			FfData ff(&worker.initvals, cell);

			for (int i = 0; i < ff.width; i++) {
				ConstCandidate cand = fold_const_inputs(ff, i);
				if (cand.val == State::Sm)
					continue;

				if (!cand.needs_proof()) {
					commit_const(const_bits, cell, i, ff.sig_q[i], cand.val);
					continue;
				}

				if (!worker.opt.sat)
					continue;

				ConstObligation ob;
				ob.cell = cell;
				ob.idx = i;
				ob.val = cand.val;
				ob.q = ff.sig_q[i];

				bool feasible = true;
				for (auto &target : cand.targets)
					feasible = feasible && add_const_target(ob, target);
				if (!feasible)
					continue;

				obligations.push_back(std::move(ob));
			}
		}

		return obligations;
	}

	int build_const_batch(QuickConeSat &qcsat, std::vector<ConstObligation> &obligations, int batch_begin)
	{
		int64_t cells_charged = 0;
		int batch_end = batch_begin;

		while (batch_end < GetSize(obligations) && !worker.warn_if_budget_spent()) {
			auto &ob = obligations[batch_end];
			if (ob.status != ConstObligation::Pending) {
				batch_end++;
				continue;
			}
			if (batch_end > batch_begin && GetSize(qcsat.imported_cells) >= sat_batch_cells)
				break;
			ob.q_lit = qcsat.importSigBit(ob.q);
			int vlit = qcsat.ez->value(ob.val == State::S1);
			std::vector<int> differ;
			for (auto &target : ob.targets) {
				int loads = qcsat.ez->AND(import_level(qcsat, target.ce, target.pol_ce),
						qcsat.ez->NOT(import_level(qcsat, target.srst, target.pol_srst)));
				// a free input differs whenever it loads, so a model drops every bit loading with
				// it, not only the ones its arbitrary input values happen to move
				qcsat.prepare();
				int ne = free_input(qcsat, target) ? qcsat.ez->CONST_TRUE :
						qcsat.ez->NOT(qcsat.ez->IFF(import_level(qcsat, target.sig, true), vlit));
				differ.push_back(qcsat.ez->AND(loads, ne));
			}
			ob.differ_lit = qcsat.ez->expression(ezSAT::OpOr, differ);
			qcsat.prepare();
			cells_charged = worker.sat_budget.charge_import(qcsat, cells_charged);
			batch_end++;
		}

		return batch_end;
	}

	// sweep the batch under the cheap screening cap first, then re-sweep the
	// still-undecided obligations with the full remaining budget
	void sweep_const_batch(QuickConeSat &qcsat, std::vector<ConstObligation> &obligations,
			int batch_begin, int batch_end, int64_t screen_cap)
	{
		for (int64_t cap : {screen_cap, (int64_t)0}) {
			bool all_resolved = true;

			// watch every pending obligation in the batch
			ConstWatchList watches;
			for (int obi = batch_begin; obi < batch_end; obi++) {
				auto &ob = obligations[obi];
				if (ob.status == ConstObligation::Pending)
					watches.watch(ob);
			}

			for (int obi = batch_begin; obi < batch_end; obi++) {
				auto &ob = obligations[obi];
				if (ob.status != ConstObligation::Pending)
					continue;
				if (worker.warn_if_budget_spent())
					return;
				bool given_up = resolve_const_obligation(qcsat, cap, ob, watches);
				if (given_up)
					all_resolved = false;
			}

			if (all_resolved)
				return;
		}
	}

	// one literal for every candidate still standing holding its value. As one
	// assumption per candidate, each would be its own MiniSat decision level
	int joint_hypo(QuickConeSat &qcsat, std::vector<ConstObligation> &obligations)
	{
		std::vector<int> holds;
		for (auto &ob : obligations)
			if (ob.status != ConstObligation::Dropped)
				holds.push_back(qcsat.ez->IFF(qcsat.importSigBit(ob.q), qcsat.ez->value(ob.val == State::S1)));
		return qcsat.ez->expression(ezSAT::OpAnd, holds);
	}

	// assume every candidate still standing holds and ask whether any pending one in
	// the batch can move. One query covers the batch (one per candidate would repeat
	// per dependency level): each model drops what it moves, and unsat holds the
	// rest. A drop only retires its activation literal, and the stale hypothesis is
	// rebuilt to confirm an unsat. Returns false once the budget is down to reserve
	bool sweep_joint_batch(QuickConeSat &qcsat, std::vector<ConstObligation> &obligations,
			int batch_begin, int batch_end, int64_t reserve)
	{
		ConstWatchList watches;
		std::vector<int> moves;
		for (int obi = batch_begin; obi < batch_end; obi++) {
			auto &ob = obligations[obi];
			if (ob.status != ConstObligation::Pending)
				continue;
			ob.act_lit = qcsat.ez->literal();
			qcsat.ez->freeze(ob.act_lit);
			watches.watch(ob);
			moves.push_back(qcsat.ez->AND(ob.act_lit, ob.differ_lit));
		}
		if (moves.empty())
			return true;

		int any = qcsat.ez->expression(ezSAT::OpOr, moves);
		int hypo = joint_hypo(qcsat, obligations);
		bool stale = false;
		while (true) {
			int64_t cap = 0;
			if (worker.sat_budget.enabled() && (cap = worker.sat_budget.remaining - reserve) <= 0)
				return false;
			std::vector<bool> model;
			auto res = worker.sat_budget.solve(qcsat, cap, watches.exprs, model, {hypo, any});
			if (res == SatEffortBudget::Result::LimitReached)
				return false;
			if (res == SatEffortBudget::Result::Unsat && stale) {
				hypo = joint_hypo(qcsat, obligations);
				stale = false;
			} else if (res == SatEffortBudget::Result::Unsat) {
				for (int obi = batch_begin; obi < batch_end; obi++)
					if (obligations[obi].status == ConstObligation::Pending)
						obligations[obi].status = ConstObligation::Held;
				return true;
			} else {
				for (auto ob : watches.drop_disproven(model))
					qcsat.ez->assume(qcsat.ez->NOT(ob->act_lit));
				stale = true;
			}
		}
	}

	// prove or drop the pending obligations batch by batch, stopping early on an
	// exhausted budget; returns the number of batches. A joint sweep down to
	// reserve clears joint, and that batch goes on per bit in the same solver, so
	// its imports are paid once, as do the batches after it
	int sweep_batches(std::vector<ConstObligation> &obligations, int64_t screen_cap, int64_t reserve, bool &joint)
	{
		ModWalker &modwalker = worker.get_modwalker();
		int batches = 0;
		for (int batch_begin = 0; batch_begin < GetSize(obligations) && !worker.warn_if_budget_spent(); batches++) {
			QuickConeSat qcsat(modwalker);
			int batch_end = build_const_batch(qcsat, obligations, batch_begin);
			if (joint && !sweep_joint_batch(qcsat, obligations, batch_begin, batch_end, reserve))
				joint = false;
			if (!joint)
				sweep_const_batch(qcsat, obligations, batch_begin, batch_end, screen_cap);
			batch_begin = batch_end;
		}
		return batches;
	}

	// sat: prove or drop the pending obligations in place. Joint passes assume every
	// candidate still standing, like eqbits' classes, which also proves flops that
	// hold each other constant. Their proofs stand only once a pass completes, so they
	// get half the budget; if they run out, the per-bit pass, whose proofs stand
	// alone, takes the rest. Joint counterexamples hold per bit too, so drops stay
	void solve_const_obligations(std::vector<ConstObligation> &obligations)
	{
		log_assert(worker.opt.sat);
		int64_t num_queries = GetSize(obligations);
		if (num_queries == 0)
			return;

		// screening cap
		int64_t screen_cap = 0;
		if (worker.sat_budget.enabled()) {
			// scale down when we can't afford a full screening round
			screen_cap = max((int64_t)20000, min((int64_t)200000, worker.sat_budget.total / (4 * num_queries)));
		}

		auto standing = [&]() {
			int n = 0;
			for (auto &ob : obligations)
				n += ob.status != ConstObligation::Dropped;
			return n;
		};
		int64_t reserve = worker.sat_budget.remaining / 2;
		bool joint = true;
		for (bool again = true; again; ) {
			int before = standing();
			int batches = sweep_batches(obligations, screen_cap, reserve, joint);
			// a pending candidate's batch ran out of budget before its sweep, and a
			// later batch's drop weakens the hypothesis an earlier batch held under
			for (auto &ob : obligations)
				joint = joint && ob.status != ConstObligation::Pending;
			again = joint && batches > 1 && standing() < before;
			for (auto &ob : obligations)
				if (ob.status == ConstObligation::Held)
					ob.status = joint && !again ? ConstObligation::Proven : ConstObligation::Pending;
		}

		// what an unfinished joint pass held goes per bit too
		if (!joint)
			sweep_batches(obligations, screen_cap, 0, joint);
	}

	bool run_constbits()
	{
		dict<Cell *, pool<int>> const_bits;

		std::vector<ConstObligation> obligations = fold_const_bits(const_bits);

		if (worker.opt.sat) {
			solve_const_obligations(obligations);
			for (auto &ob : obligations)
				if (ob.status == ConstObligation::Proven)
					commit_const(const_bits, ob.cell, ob.idx, ob.q, ob.val);
		}

		for (auto &[cell, drop] : const_bits)
			worker.remove_ff_bits(cell, drop);

		return !const_bits.empty();
	}
};

PRIVATE_NAMESPACE_END

YOSYS_NAMESPACE_BEGIN

bool OptDffWorker::run_constbits()
{
	return ConstBitsContext(*this).run_constbits();
}

YOSYS_NAMESPACE_END
