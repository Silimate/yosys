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

// Bit-parallel random simulation used as a cheap pre-filter for equivalence
struct BitSim {
	Module *module;
	SigMap &sigmap;
	ModWalker &modwalker;
	dict<SigBit, uint64_t> sim_vals;
	uint64_t rng_state;
	int max_depth;
	int evals_left;
	// evaluate word-level logic too; random values split classes of distinct signals
	// better, but miss that differently built enables agree
	bool word_cells;

	BitSim(Module *m, SigMap &sm, ModWalker &mw, bool word_cells = false)
		: module(m), sigmap(sm), modwalker(mw), rng_state(1337), word_cells(word_cells)
	{
		max_depth = module->design->scratchpad_get_int("opt_dff.sim_depth", 10000);
		evals_left = module->design->scratchpad_get_int("opt_dff.sim_evals", 1000000);
	}

	uint64_t next_rand() {
		uint32_t lo = mkhash_xorshift((uint32_t)rng_state);
		uint32_t hi = mkhash_xorshift((uint32_t)(rng_state >> 32) ^ lo);
		rng_state = ((uint64_t)hi << 32) | lo;
		return rng_state;
	}

	uint64_t eval_bit(SigBit b, int depth = 0) {
		SigBit mapped = sigmap(b);
		if (mapped == State::S0) return 0ULL;
		if (mapped == State::S1) return ~0ULL;
		if (mapped == State::Sx || mapped == State::Sz) return 0ULL;

		auto it = sim_vals.find(mapped);
		if (it != sim_vals.end()) return it->second;

		// Failsafe for huge designs
		if (depth >= max_depth || evals_left <= 0) {
			uint64_t r = next_rand();
			sim_vals[mapped] = r;
			return r;
		}
		evals_left--;

		// pre-seed to break combinational loops
		sim_vals[mapped] = 0;
		uint64_t res = 0;

		auto drv = modwalker.signal_drivers.find(mapped);
		if (drv == modwalker.signal_drivers.end() || drv->second.empty()) {
			res = next_rand();
		} else {
			auto driver = *drv->second.begin();
			Cell *cell = driver.cell;

			if (cell->is_builtin_ff()) {
				res = next_rand();
			} else if (cell->type == ID($_AND_)) {
				res = eval_bit(cell->getPort(ID::A)[0], depth+1) & eval_bit(cell->getPort(ID::B)[0], depth+1);
			} else if (cell->type == ID($_OR_)) {
				res = eval_bit(cell->getPort(ID::A)[0], depth+1) | eval_bit(cell->getPort(ID::B)[0], depth+1);
			} else if (cell->type == ID($_XOR_)) {
				res = eval_bit(cell->getPort(ID::A)[0], depth+1) ^ eval_bit(cell->getPort(ID::B)[0], depth+1);
			} else if (cell->type == ID($_NOT_)) {
				res = ~eval_bit(cell->getPort(ID::A)[0], depth+1);
			} else if (cell->type == ID($_MUX_)) {
				uint64_t s = eval_bit(cell->getPort(ID::S)[0], depth+1);
				uint64_t a = eval_bit(cell->getPort(ID::A)[0], depth+1);
				uint64_t b = eval_bit(cell->getPort(ID::B)[0], depth+1);
				res = (a & ~s) | (b & s);
			} else if (cell->type == ID($mux)) {
				uint64_t s = eval_bit(cell->getPort(ID::S)[0], depth+1);
				uint64_t a = eval_bit(cell->getPort(ID::A)[driver.offset], depth+1);
				uint64_t b = eval_bit(cell->getPort(ID::B)[driver.offset], depth+1);
				res = (a & ~s) | (b & s);
			} else if (word_cells && cell->type.in(ID($not), ID($and), ID($or), ID($xor), ID($xnor))) {
				uint64_t a = eval_input(cell, ID::A, driver.offset, depth);
				uint64_t b = cell->type == ID($not) ? 0 : eval_input(cell, ID::B, driver.offset, depth);
				res = cell->type == ID($not) ? ~a : cell->type == ID($and) ? a & b : cell->type == ID($or) ? a | b :
						cell->type == ID($xor) ? a ^ b : ~(a ^ b);
			} else if (word_cells && cell->type.in(ID($reduce_and), ID($reduce_or), ID($reduce_bool), ID($reduce_xor),
					ID($reduce_xnor), ID($logic_not), ID($logic_and), ID($logic_or), ID($eq), ID($ne))) {
				res = driver.offset ? 0 : eval_flag(cell, depth);  // higher Y bits are zero
			} else {
				res = next_rand();
			}
		}

		sim_vals[mapped] = res;
		return res;
	}

	// bit i of a word-level cell's input, sign- or zero-extended past its width
	uint64_t eval_input(Cell *cell, IdString port, int i, int depth) {
		const SigSpec &sig = cell->getPort(port);
		if (i < GetSize(sig))
			return eval_bit(sig[i], depth+1);
		bool is_signed = cell->getParam(port == ID::A ? ID::A_SIGNED : ID::B_SIGNED).as_bool();
		return is_signed && !sig.empty() ? eval_bit(sig.msb(), depth+1) : 0;
	}

	// the 1-bit result of a reduction, logic or equality cell
	uint64_t eval_flag(Cell *cell, int depth) {
		auto any = [&](IdString port) {
			uint64_t r = 0;
			for (auto bit : cell->getPort(port))
				r |= eval_bit(bit, depth+1);
			return r;
		};
		IdString type = cell->type;
		if (type.in(ID($eq), ID($ne))) {
			uint64_t diff = 0;
			int width = std::max(GetSize(cell->getPort(ID::A)), GetSize(cell->getPort(ID::B)));
			for (int i = 0; i < width; i++)
				diff |= eval_input(cell, ID::A, i, depth) ^ eval_input(cell, ID::B, i, depth);
			return type == ID($eq) ? ~diff : diff;
		}
		if (type.in(ID($reduce_xor), ID($reduce_xnor))) {
			uint64_t r = 0;
			for (auto bit : cell->getPort(ID::A))
				r ^= eval_bit(bit, depth+1);
			return type == ID($reduce_xor) ? r : ~r;
		}
		if (type == ID($reduce_and)) {
			uint64_t r = ~0ULL;
			for (auto bit : cell->getPort(ID::A))
				r &= eval_bit(bit, depth+1);
			return r;
		}
		if (type.in(ID($reduce_or), ID($reduce_bool)))
			return any(ID::A);
		if (type == ID($logic_not))
			return ~any(ID::A);
		return type == ID($logic_and) ? any(ID::A) & any(ID::B) : any(ID::A) | any(ID::B);
	}
};

// concrete 0/1 bit, as opposed to x/z
bool is_def(State s) {
	return s == State::S0 || s == State::S1;
}

struct EqBitsContext
{
	OptDffWorker &worker;

	// The first pass, mixes off, only classes flops whose enable and sync reset are mapped
	// alike, and compares their D. The second takes classes that mix mappings, which need
	// the whole next state, and keeps the small ones: random simulation rarely fires the
	// decoded enables of a register bank, so it can't split a big one, and SAT pays
	bool mixes;
	static constexpr int max_mixed_class = 32;

	EqBitsContext(OptDffWorker &worker, bool mixes) : worker(worker), mixes(mixes) { }

	struct EqBit {
		Cell *cell;
		int idx;
		SigBit q;
	};

	// NOTE: This intentionally duplicates a subset of FfData, as flattening just the
	// fields that matter for merging into a single comparable/hashable key is cheaper
	struct SigKey {
		enum Flag : uint16_t {
			InitOne     = 1u << 0,
			InitX       = 1u << 1,
			PolClk      = 1u << 2,
			PolArst     = 1u << 3,
			PolAload    = 1u << 4,
			PolClr      = 1u << 5,
			PolSet      = 1u << 6,
		};

		// the enable and sync reset are keyed apart (CtrlKey), which the mixing pass leaves out
		SigBit clk, arst, aload, clr, set;
		IdString cell_type;  // for SR
		uint16_t flags;

		bool operator==(const SigKey &o) const {
			return flags == o.flags && clk == o.clk && arst == o.arst
				&& aload == o.aload && clr == o.clr && set == o.set && cell_type == o.cell_type;
		}

		Hasher hash_into(Hasher h) const {
			h.eat(flags);
			h.eat(clk);
			h.eat(arst);
			h.eat(aload);
			h.eat(clr);
			h.eat(set);
			h.eat(cell_type);
			return h;
		}
	};

	// how a bit's enable and sync reset are mapped, which the class key leaves out
	using CtrlKey = std::tuple<SigBit, SigBit, int>;

	struct EqCandidates {
		std::vector<EqBit> bits;
		std::vector<CtrlKey> ctrls;
		dict<Cell *, FfData> ffs;
		std::vector<std::vector<int>> classes;
	};

	EqCandidates gather_initial_eq_classes()
	{
		EqCandidates cand;
		std::vector<SigKey> keys;

		// Collect FF bits eligible for merging
		for (auto cell : worker.module->selected_cells()) {
			if (!cell->is_builtin_ff())
				continue;

			FfData ff(&worker.initvals, cell);
			if (!ff.has_clk && !ff.has_gclk)
				continue;

			cand.ffs.emplace(cell, ff);

			for (int i = 0; i < ff.width; i++) {
				// Skip bits whose reset value is undefined (x)
				if (ff.has_srst && !is_def(ff.val_srst[i])) continue;
				if (ff.has_arst && !is_def(ff.val_arst[i])) continue;

				// Class members are assumed equal in the current cycle and proven equal in the next, which needs
				// a base case anchoring them to a common known value
				bool def_init = is_def(ff.val_init[i]);
				if (!def_init && !ff.has_srst && !ff.has_arst)
					continue;

				SigKey k = {};

				// Flags
				if (def_init && ff.val_init[i] == State::S1)
					k.flags |= SigKey::InitOne;
				else if (!def_init)
					k.flags |= SigKey::InitX;

				if (ff.has_clk) {
					k.clk = ff.sig_clk;
					if (ff.pol_clk) k.flags |= SigKey::PolClk;
				}
				if (ff.has_arst) {
					k.arst = ff.sig_arst;
					if (ff.pol_arst) k.flags |= SigKey::PolArst;
				}
				if (ff.has_aload) {
					k.aload = ff.sig_aload;
					if (ff.pol_aload) k.flags |= SigKey::PolAload;
				}
				if (ff.has_sr) {
					k.clr = ff.sig_clr[i];
					k.set = ff.sig_set[i];
					k.cell_type = cell->type;
					if (ff.pol_clr) k.flags |= SigKey::PolClr;
					if (ff.pol_set) k.flags |= SigKey::PolSet;
				}

				cand.bits.push_back({cell, i, ff.sig_q[i]});
				// polarities are only set for controls the flop has
				bool ce = ff.has_ce, srst = ff.has_srst;
				cand.ctrls.push_back({ce ? SigBit(ff.sig_ce) : SigBit(), srst ? SigBit(ff.sig_srst) : SigBit(),
						ce + 2 * (ce && ff.pol_ce) + 4 * srst + 8 * (srst && ff.pol_srst) + 16 * (ce && srst && ff.ce_over_srst)});
				keys.push_back(k);
			}
		}

		dict<std::pair<SigKey, CtrlKey>, std::vector<int>> buckets;
		for (int i = 0; i < GetSize(cand.bits); i++)
			buckets[{keys[i], mixes ? CtrlKey() : cand.ctrls[i]}].push_back(i);

		for (auto &kv : buckets)
			if (GetSize(kv.second) >= 2 && (!mixes || (GetSize(kv.second) <= max_mixed_class && mixed(cand, kv.second))))
				cand.classes.push_back(std::move(kv.second));

		return cand;
	}

	void filter_classes_sim(EqCandidates &cand)
	{
		// mixed classes need their enables evaluated, which takes word-level logic
		BitSim sim(worker.module, worker.sigmap, worker.get_modwalker(), mixes);

		// Assume same class
		for (auto &cls : cand.classes) {
			uint64_t class_q_val = sim.next_rand();
			for (int idx : cls) {
				sim.sim_vals[worker.sigmap(cand.bits[idx].q)] = class_q_val;
			}
		}

		std::vector<std::vector<int>> refined_classes;
		for (auto &cls : cand.classes) {
			dict<uint64_t, std::vector<int>> sim_buckets;
			for (int idx : cls) {
				const EqBit &eb = cand.bits[idx];
				const FfData &ff = cand.ffs.at(eb.cell);
				uint64_t n_val = sim.eval_bit(ff.sig_d[eb.idx]);

				// flops mapped alike compare D, which splits more; mixed ones need the enable
				// and sync reset by priority (a $sdffce resets only while enabled)
				auto sync_reset = [&](uint64_t n) {
					uint64_t srst = sim.eval_bit(ff.sig_srst);
					if (!ff.pol_srst) srst = ~srst;
					uint64_t srst_val = (ff.val_srst[eb.idx] == State::S1) ? ~0ULL : 0ULL;
					return (n & ~srst) | (srst_val & srst);
				};
				bool srst_in_ce = mixes && ff.has_srst && ff.has_ce && ff.ce_over_srst;
				if (srst_in_ce)
					n_val = sync_reset(n_val);
				if (mixes && ff.has_ce) {
					uint64_t ce = sim.eval_bit(ff.sig_ce);
					if (!ff.pol_ce) ce = ~ce;
					n_val = (n_val & ce) | (sim.eval_bit(eb.q) & ~ce);
				}
				if (ff.has_srst && !srst_in_ce)
					n_val = sync_reset(n_val);

				if (ff.has_aload) {
					uint64_t al = sim.eval_bit(ff.sig_aload);
					if (!ff.pol_aload) al = ~al;
					uint64_t ad = sim.eval_bit(ff.sig_ad[eb.idx]);
					n_val = (n_val & ~al) | (ad & al);
				}
				if (ff.has_arst) {
					uint64_t ar = sim.eval_bit(ff.sig_arst);
					if (!ff.pol_arst) ar = ~ar;
					uint64_t ar_val = (ff.val_arst[eb.idx] == State::S1) ? ~0ULL : 0ULL;
					n_val = (n_val & ~ar) | (ar_val & ar);
				}
				if (ff.has_sr) {
					uint64_t clr = sim.eval_bit(ff.sig_clr[eb.idx]);
					if (!ff.pol_clr) clr = ~clr;
					uint64_t set = sim.eval_bit(ff.sig_set[eb.idx]);
					if (!ff.pol_set) set = ~set;
					n_val = ~clr & (set | n_val);
				}

				sim_buckets[n_val].push_back(idx);
			}

			for (auto &kv : sim_buckets)
				if (GetSize(kv.second) >= 2)
					refined_classes.push_back(std::move(kv.second));
		}

		cand.classes = std::move(refined_classes);
	}

	// whether a class holds flops mapped with different enables or sync resets
	static bool mixed(const EqCandidates &cand, const std::vector<int> &cls)
	{
		for (int idx : cls)
			if (cand.ctrls[idx] != cand.ctrls[cls[0]])
				return true;
		return false;
	}

	void drop_all_classes(EqCandidates &cand)
	{
		log("opt_dff -sat: skipping all equivalent-flip-flop merges in module %s (solver effort budget "
				"exhausted before the equivalences could be proven).\n", log_id(worker.module));
		cand.classes.clear();
	}

	void filter_classes_sat(EqCandidates &cand)
	{
		auto &classes = cand.classes;
		auto &bits = cand.bits;
		QuickConeSat qcsat(worker.get_modwalker());
		std::vector<int> q_lit(bits.size(), -1);
		std::vector<int> n_lit(bits.size(), -1);
		// Mixing, n_lit is the whole next state, so it has the bit's own Q in it. s_lit has
		// one shared literal for every bit's Q instead: two bits whose ones match agree
		// whenever their Qs do, so the pair needs no query
		std::vector<int> s_lit(bits.size(), -1);
		int hold = mixes ? qcsat.ez->literal() : 0;

		// Build the next-state function n_lit[idx] of every candidate bit by
		// folding the FF's control logic on top of the D input (-> next value)
		int64_t cells_charged = 0;

		// Two bits are equivalent if their next states always agree whenever their
		// current states (and those of every other candidate pair) agree
		for (auto &cls : classes) {
			if (worker.warn_if_budget_spent())
				return drop_all_classes(cand);
			for (int idx : cls) {
				const EqBit &eb = bits[idx];
				const FfData &ff = cand.ffs.at(eb.cell);
				q_lit[idx] = qcsat.importSigBit(eb.q);

				auto next_state = [&](int q) {
					int n = qcsat.importSigBit(ff.sig_d[eb.idx]);

					// the enable and sync reset by priority: a $sdffce resets only while enabled
					auto sync_reset = [&](int n) {
						int srst = qcsat.importSigBit(ff.sig_srst);
						if (!ff.pol_srst) srst = qcsat.ez->NOT(srst);
						return qcsat.ez->ITE(srst, qcsat.ez->value(ff.val_srst[eb.idx] == State::S1), n);
					};
					bool srst_in_ce = mixes && ff.has_srst && ff.has_ce && ff.ce_over_srst;
					if (srst_in_ce)
						n = sync_reset(n);
					if (mixes && ff.has_ce) {
						int ce = qcsat.importSigBit(ff.sig_ce);
						if (!ff.pol_ce) ce = qcsat.ez->NOT(ce);
						n = qcsat.ez->ITE(ce, n, q);
					}
					if (ff.has_srst && !srst_in_ce)
						n = sync_reset(n);

					if (ff.has_aload) {
						int al = qcsat.importSigBit(ff.sig_aload);
						if (!ff.pol_aload) al = qcsat.ez->NOT(al);
						n = qcsat.ez->ITE(al, qcsat.importSigBit(ff.sig_ad[eb.idx]), n);
					}
					if (ff.has_arst) {
						int ar = qcsat.importSigBit(ff.sig_arst);
						if (!ff.pol_arst) ar = qcsat.ez->NOT(ar);
						n = qcsat.ez->ITE(ar, qcsat.ez->value(ff.val_arst[eb.idx] == State::S1), n);
					}
					if (ff.has_sr) {
						int clr = qcsat.importSigBit(ff.sig_clr[eb.idx]);
						if (!ff.pol_clr) clr = qcsat.ez->NOT(clr);
						int set = qcsat.importSigBit(ff.sig_set[eb.idx]);
						if (!ff.pol_set) set = qcsat.ez->NOT(set);
						n = qcsat.ez->AND(qcsat.ez->NOT(clr), qcsat.ez->OR(set, n));
					}
					return n;
				};
				n_lit[idx] = next_state(q_lit[idx]);
				s_lit[idx] = mixes ? next_state(hold) : n_lit[idx];
			}
			qcsat.prepare();
			cells_charged = worker.sat_budget.charge_import(qcsat, cells_charged);
		}

		// Assume the induction hypo (that every current class is internally equal in the present cycle), and try
		// to prove that the members of each class therefore also agree in the next cycle

		// A class survives only if no counterexample exists under that hypo, so combined with the common init/reset
		// value that every class shares, this makes the equality an inductive invariant -> bits are eq and safe to merge
		std::vector<int> worklist;
		std::vector<bool> in_worklist(GetSize(classes), true);

		for (int i = 0; i < GetSize(classes); i++)
			worklist.push_back(i);

		// The hypo is one literal, rebuilt only when a split weakens it. As one assumption per
		// member pair, each pair became its own MiniSat decision level, and once the learnt
		// clauses outgrow MiniSat's limit it sorts all of them (reduceDB) before every decision.
		// The propagation budget never sees that: on a masked adder it was minutes of sorting.
		int hypo = 0;

		while (!worklist.empty()) {
			int cls_idx = worklist.back();
			worklist.pop_back();
			in_worklist[cls_idx] = false;

			auto &cls = classes[cls_idx];
			if (GetSize(cls) < 2) continue;

			// Induction hypo: assume every candidate class is equal
			if (!hypo) {
				std::vector<int> eqs;
				for (auto &c : classes) {
					if (GetSize(c) < 2) continue;
					int rep = c[0];
					for (int k = 1; k < GetSize(c); k++)
						eqs.push_back(qcsat.ez->IFF(q_lit[rep], q_lit[c[k]]));
				}
				hypo = qcsat.ez->expression(ezSAT::OpAnd, eqs);
			}
			std::vector<int> assumptions = {hypo};

			// Scan the class members against the representative and issue a query per pair,
			// stopping early at the first counterexample, which is reused to split the entire
			// class at once
			int rep = cls[0];
			for (int i = 1; i < GetSize(cls); i++) {
				if (s_lit[rep] == s_lit[cls[i]])
					continue;

				if (worker.warn_if_budget_spent())
					return drop_all_classes(cand);

				// Can the next state of the rep and this member ever differ?
				int query = qcsat.ez->XOR(n_lit[rep], n_lit[cls[i]]);
				// Capture every member's next-state value in that model so one counterexample
				// partitions the whole class
				std::vector<int> modelExprs;
				for (int b : cls)
					modelExprs.push_back(n_lit[b]);

				std::vector<bool> modelVals;
				assumptions.push_back(query);

				auto res = worker.sat_budget.solve(qcsat, 0, modelExprs, modelVals, assumptions);

				if (res == SatEffortBudget::Result::LimitReached) {
					worker.warn_if_budget_spent();
					return drop_all_classes(cand);
				}

				if (res == SatEffortBudget::Result::Sat) {
					// SAT -> partition entire class
					std::vector<int> sub0;
					std::vector<int> sub1;

					for (int b_idx = 0; b_idx < GetSize(cls); b_idx++) {
						if (modelVals[b_idx])
							sub1.push_back(cls[b_idx]);
						else
							sub0.push_back(cls[b_idx]);
					}

					classes[cls_idx] = std::move(sub0);
					classes.push_back(std::move(sub1));
					in_worklist.push_back(false);

					// Partition was split -> the induction hypo weakened
					hypo = 0;
					for (int j = 0; j < GetSize(classes); j++) {
						if (GetSize(classes[j]) >= 2 && !in_worklist[j]) {
							worklist.push_back(j);
							in_worklist[j] = true;
						}
					}

					break; // Process new splits
				}

				assumptions.pop_back(); // Remove query for the next pairwise check if UNSAT
			}
		}
	}

	bool apply_eq_merges(const EqCandidates &cand)
	{
		bool any_change = false;
		dict<Cell *, pool<int>> remove_bits;

		// Drive every non-rep Q from its class rep, drop merged bits from their FFs
		for (auto &cls : cand.classes) {
			if (GetSize(cls) < 2)
				continue;
			SigBit rep_q = cand.bits[cls[0]].q;
			any_change = true;
			for (int k = 1; k < GetSize(cls); k++) {
				const EqBit &eb = cand.bits[cls[k]];
				worker.initvals.remove_init(eb.q);
				worker.module->connect(eb.q, rep_q);
				remove_bits[eb.cell].insert(eb.idx);
			}
		}

		for (auto &[cell, drop] : remove_bits)
			worker.remove_ff_bits(cell, drop);

		return any_change;
	}

	bool run_eqbits()
	{
		EqCandidates cand = gather_initial_eq_classes();
		if (cand.classes.empty())
			return false;

		// Simulation prepass
		filter_classes_sim(cand);
		if (cand.classes.empty())
			return false;

		// SAT prove
		filter_classes_sat(cand);
		if (cand.classes.empty())
			return false;

		return apply_eq_merges(cand);
	}
};

PRIVATE_NAMESPACE_END

YOSYS_NAMESPACE_BEGIN

bool OptDffWorker::run_eqbits()
{
	bool changed = EqBitsContext(*this, false).run_eqbits();
	if (changed)
		refresh_after_edits();
	bool mixed = EqBitsContext(*this, true).run_eqbits();
	return changed || mixed;
}

YOSYS_NAMESPACE_END
