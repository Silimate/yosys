/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Akash Levy        <akash@silimate.com>
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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/ff.h"
#include "kernel/ffinit.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Bit lattice: S0 and S1 are known, Sx is "no information". Sz is never produced.
static inline bool known(State s) { return s == State::S0 || s == State::S1; }
static inline State from_bool(bool b) { return b ? State::S1 : State::S0; }

struct OptSeqConstWorker {
	Module *module;
	SigMap sigmap;
	FfInitVals initvals;

	dict<SigBit, Cell *> bit_drivers;
	std::vector<Cell *> ffs;

	// Current hypothesis for the flop output bits still believed constant, and the
	// per-iteration memo of everything derived from it.
	dict<SigBit, State> hyp;
	dict<SigBit, State> memo;

	// Guard against blowing the stack on a pathologically deep cone. Bailing out
	// reads back as unknown, which only costs optimizations.
	static const int MAX_DEPTH = 4096;
	int depth = 0;

	int replaced = 0;

	OptSeqConstWorker(Module *m) : module(m), sigmap(m), initvals(&sigmap, m)
	{
		for (auto cell : module->cells()) {
			for (auto &conn : cell->connections())
				if (cell->output(conn.first))
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							bit_drivers[bit] = cell;
			if (cell->is_builtin_ff())
				ffs.push_back(cell);
		}
	}

	// ---------------------------------------------------------------- evaluation

	// One input bit of a cell, widened to the output width the way RTLIL cells do:
	// out of range is the sign bit when signed and zero otherwise.
	State in_bit(const SigSpec &sig, int i, bool is_signed)
	{
		int w = GetSize(sig);
		if (w == 0)
			return State::Sx;
		if (i >= w)
			return is_signed ? bit_value(sig[w - 1]) : State::S0;
		return bit_value(sig[i]);
	}

	// Ripple-add A + B (+carry_in), with B optionally inverted for subtraction. The
	// low bits stay exact as long as both operands are known there, which is the
	// whole point: a pointer stepped by an aligned constant keeps its zero tail even
	// though the high bits are unknown.
	void eval_addsub(Cell *cell, const SigSpec &y, bool sub)
	{
		SigSpec a = sigmap(cell->getPort(ID::A));
		SigSpec b = sigmap(cell->getPort(ID::B));
		bool sa = cell->getParam(ID::A_SIGNED).as_bool();
		bool sb = cell->getParam(ID::B_SIGNED).as_bool();
		State carry = sub ? State::S1 : State::S0;
		for (int i = 0; i < GetSize(y); i++) {
			State av = in_bit(a, i, sa), bv = in_bit(b, i, sb);
			if (sub && known(bv))
				bv = from_bool(bv == State::S0);
			if (!known(av) || !known(bv) || !known(carry)) {
				// Carry is lost, so this bit and everything above it is unknown.
				for (int j = i; j < GetSize(y); j++)
					memo[y[j]] = State::Sx;
				return;
			}
			int sum = (av == State::S1) + (bv == State::S1) + (carry == State::S1);
			memo[y[i]] = from_bool(sum & 1);
			carry = from_bool(sum >= 2);
		}
	}

	// Y bit is v if every arm that could be selected agrees on v. Covers the case
	// that matters here: a select whose condition is unknown but whose arms are all
	// zero in the bits we care about.
	State eval_mux_bit(const std::vector<SigSpec> &arms, const SigSpec &sel, int i)
	{
		// A known select picks its arm outright.
		if (GetSize(sel) == 1) {
			State s = bit_value(sel[0]);
			if (known(s))
				return in_bit(arms[s == State::S1 ? 1 : 0], i, false);
		}
		State v = State::Sx;
		for (auto &arm : arms) {
			State av = in_bit(arm, i, false);
			if (!known(av))
				return State::Sx;
			if (!known(v))
				v = av;
			else if (v != av)
				return State::Sx;
		}
		return v;
	}

	// Compute every output bit of one cell and memoize it.
	void eval_cell(Cell *cell)
	{
		SigSpec y = cell->hasPort(ID::Y) ? sigmap(cell->getPort(ID::Y)) : SigSpec();
		// Default to unknown up front, which also breaks combinational cycles: a
		// bit reached again while being computed reads back as Sx.
		for (auto bit : y)
			memo[bit] = State::Sx;
		if (GetSize(y) == 0)
			return;

		IdString t = cell->type;
		if (t.in(ID($add), ID($sub))) {
			eval_addsub(cell, y, t == ID($sub));
			return;
		}
		if (t.in(ID($mux), ID($bwmux))) {
			SigSpec a = sigmap(cell->getPort(ID::A)), b = sigmap(cell->getPort(ID::B));
			SigSpec s = sigmap(cell->getPort(ID::S));
			for (int i = 0; i < GetSize(y); i++)
				memo[y[i]] = t == ID($mux)
						     ? eval_mux_bit({a, b}, s, i)
						     : eval_mux_bit({a, b}, s.extract(i, 1), i);
			return;
		}
		if (t == ID($pmux)) {
			SigSpec a = sigmap(cell->getPort(ID::A)), b = sigmap(cell->getPort(ID::B));
			int w = GetSize(y), n = GetSize(sigmap(cell->getPort(ID::S)));
			std::vector<SigSpec> arms = {a};
			for (int k = 0; k < n; k++)
				arms.push_back(b.extract(k * w, w));
			for (int i = 0; i < w; i++)
				memo[y[i]] = eval_mux_bit(arms, SigSpec(), i);
			return;
		}
		if (t.in(ID($and), ID($or), ID($xor), ID($xnor), ID($not), ID($pos))) {
			SigSpec a = sigmap(cell->getPort(ID::A));
			SigSpec b = t.in(ID($not), ID($pos)) ? SigSpec() : sigmap(cell->getPort(ID::B));
			bool sa = cell->getParam(ID::A_SIGNED).as_bool();
			bool sb = t.in(ID($not), ID($pos)) ? false : cell->getParam(ID::B_SIGNED).as_bool();
			for (int i = 0; i < GetSize(y); i++) {
				State av = in_bit(a, i, sa);
				if (t == ID($pos)) { memo[y[i]] = av; continue; }
				if (t == ID($not)) {
					memo[y[i]] = known(av) ? from_bool(av == State::S0) : State::Sx;
					continue;
				}
				State bv = in_bit(b, i, sb);
				if (t == ID($and))
					memo[y[i]] = (av == State::S0 || bv == State::S0) ? State::S0
						     : (known(av) && known(bv))          ? State::S1
											 : State::Sx;
				else if (t == ID($or))
					memo[y[i]] = (av == State::S1 || bv == State::S1) ? State::S1
						     : (known(av) && known(bv))          ? State::S0
											 : State::Sx;
				else if (known(av) && known(bv))
					memo[y[i]] = from_bool((av != bv) == (t == ID($xor)));
			}
			return;
		}
		if (t.in(ID($shl), ID($sshl)) && cell->getPort(ID::B).is_fully_const()) {
			SigSpec a = sigmap(cell->getPort(ID::A));
			bool sa = cell->getParam(ID::A_SIGNED).as_bool();
			int sh = cell->getPort(ID::B).as_int();
			for (int i = 0; i < GetSize(y); i++)
				memo[y[i]] = i < sh ? State::S0 : in_bit(a, i - sh, sa);
			return;
		}
		// Everything else keeps the Sx default: this analysis only needs to be
		// precise on the move-and-mask logic that pointers are built from.
	}

	State bit_value(SigBit bit)
	{
		if (!bit.wire)
			return bit.data;
		bit = sigmap(bit);
		if (!bit.wire)
			return bit.data;
		auto hit = hyp.find(bit);
		if (hit != hyp.end())
			return hit->second;
		auto mit = memo.find(bit);
		if (mit != memo.end())
			return mit->second;
		Cell *drv = bit_drivers.at(bit, nullptr);
		if (!drv) {
			memo[bit] = State::Sx;
			return State::Sx;
		}
		// A flop output not in `hyp` has already been ruled non-constant.
		if (drv->is_builtin_ff() || depth >= MAX_DEPTH) {
			memo[bit] = State::Sx;
			return State::Sx;
		}
		depth++;
		eval_cell(drv);
		depth--;
		return memo.at(bit, State::Sx);
	}

	// ------------------------------------------------------------------ fixpoint

	void run()
	{
		// Seed: every flop bit whose reset, async load or init value pins it to a
		// known constant. Sources that disagree cancel the bit out.
		std::vector<std::pair<Cell *, FfData>> ffdata;
		for (auto cell : ffs) {
			FfData ff(&initvals, cell);
			// Set/clear can force a bit either way independently of D.
			if (ff.has_sr || ff.width == 0)
				continue;
			ffdata.emplace_back(cell, ff);
			for (int i = 0; i < ff.width; i++) {
				SigBit q = sigmap(ff.sig_q[i]);
				if (!q.wire)
					continue;
				State v = State::Sx;
				bool bad = false;
				auto pin = [&](State s) {
					if (!known(s))
						return;
					if (!known(v))
						v = s;
					else if (v != s)
						bad = true;
				};
				if (GetSize(ff.val_init) > i)
					pin(ff.val_init[i]);
				if (ff.has_arst)
					pin(ff.val_arst[i]);
				if (ff.has_srst)
					pin(ff.val_srst[i]);
				if (ff.has_aload && ff.sig_ad[i].wire == nullptr)
					pin(ff.sig_ad[i].data);
				if (!bad && known(v))
					hyp[q] = v;
			}
		}

		// Greatest fixpoint: drop any bit whose next value can disagree with the
		// hypothesis. Dropping only ever weakens what the others can prove, so
		// iterating until nothing drops is sound and terminates.
		bool changed = true;
		while (changed) {
			changed = false;
			memo.clear();
			for (auto &it : ffdata) {
				FfData &ff = it.second;
				for (int i = 0; i < ff.width; i++) {
					SigBit q = sigmap(ff.sig_q[i]);
					auto hit = hyp.find(q);
					if (hit == hyp.end())
						continue;
					State v = hit->second;
					// Every way Q can be updated has to reproduce v. Holding
					// reproduces it trivially, and the reset constants were
					// already checked against v when seeding. A latch has no
					// clocked path, so only its async load can change it.
					bool ok = true;
					if (ff.has_clk || ff.has_gclk)
						ok = bit_value(ff.sig_d[i]) == v;
					if (ok && ff.has_aload)
						ok = bit_value(ff.sig_ad[i]) == v;
					if (!ok) {
						hyp.erase(q);
						changed = true;
					}
				}
			}
		}

		// Rewire: the flop keeps driving a private wire, and the signal it used to
		// drive becomes the constants plus whatever bits survive on that wire.
		// wreduce and opt_clean shrink the flop itself afterwards.
		for (auto &it : ffdata) {
			Cell *cell = it.first;
			if (!cell->hasPort(ID::Q))
				continue;
			SigSpec q = cell->getPort(ID::Q);
			int hits = 0;
			for (auto bit : q)
				if (bit.wire && hyp.count(sigmap(bit)))
					hits++;
			if (!hits)
				continue;
			SigSpec priv = module->addWire(NEW_ID, GetSize(q));
			SigSpec repl;
			for (int i = 0; i < GetSize(q); i++) {
				SigBit b = q[i];
				auto hit = b.wire ? hyp.find(sigmap(b)) : hyp.end();
				repl.append(hit != hyp.end() ? SigSpec(hit->second) : priv.extract(i, 1));
			}
			cell->setPort(ID::Q, priv);
			module->connect(q, repl);
			replaced += hits;
		}
	}
};

struct OptSeqConstPass : public Pass {
	OptSeqConstPass() : Pass("opt_seqconst", "replace provably constant flop bits with constants") {}

	void help() override {
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_seqconst [selection]\n");
		log("\n");
		log("Finds flop bits that are constant in every reachable state and replaces them\n");
		log("with that constant. A bit qualifies when its reset, async-load or init value\n");
		log("pins it to a known value and every way it can be updated reproduces that\n");
		log("value, so the property holds by induction over cycles.\n");
		log("\n");
		log("This is what makes an aligned pointer cheap. A write pointer reset to 0 and\n");
		log("only ever stepped by a power-of-two burst length keeps a zero tail forever,\n");
		log("so its low bits are constants even though the pointer itself is not. Once\n");
		log("they fold, an unrolled `for` loop scattering a burst through such a pointer\n");
		log("stops being a full crossbar and becomes a plain word write: on a customer\n");
		log("weight decompressor the array-write cone drops from 131k cells to 512.\n");
		log("\n");
		log("The analysis is a greatest fixpoint over a bit lattice, so it needs a\n");
		log("transfer function per cell rather than a solver. It is exact on the move,\n");
		log("mask and add-a-constant logic that pointers are built from ($add, $sub, the\n");
		log("bitwise cells, the mux cells and a constant $shl) and gives up on anything\n");
		log("else, which only ever costs optimizations, never soundness.\n");
		log("\n");
		log("Because the seed comes from the reset value, this assumes reset is applied\n");
		log("before the design is relied upon, as synthesis normally does. The result is\n");
		log("only equivalent over reachable states, so checking it needs sequential\n");
		log("equivalence (equiv_induct) and not a combinational miter.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing OPT_SEQCONST pass (fold provably constant flop bits).\n");

		size_t argidx = 1;
		extra_args(args, argidx, design);

		int total = 0;
		for (auto module : design->selected_modules()) {
			OptSeqConstWorker worker(module);
			worker.run();
			if (worker.replaced)
				log("Module %s: folded %d constant flop bit(s).\n",
				    log_id(module), worker.replaced);
			total += worker.replaced;
		}
		log("Folded %d constant flop bit(s).\n", total);
	}
} OptSeqConstPass;

PRIVATE_NAMESPACE_END
