/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Silimate Inc.     <akash@silimate.com>
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
 */

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include <vector>
#include "kernel/celltypes.h"
#include <cmath>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "passes/silimate/rewrite_utils.h"
#include "passes/silimate/unit_delay.h"

// opt_addcmp: fuse an adder into the comparator it feeds.
//
// A bound check spelled `a + b <cmp> c` costs a full carry-propagate adder
// followed by a comparator, but the sum itself is never needed -- only its
// order against c. Adding one carry-save level in front of the comparator
// removes the adder from that path:
//
//     (a + b) >= c   <=>   s >= ~d       with  s = a ^ b ^ ~c
//     (a + b) >  c   <=>   s >  ~d             v = maj(a, b, ~c)
//                                              d = v << 1
//
// Both operands are widened to W = max(|a|,|b|,|c|) + 1 first, so a and b
// carry a zero in the top bit and the carry out of that column, which the
// shift drops, is maj(0, 0, x) = 0. Working one bit wider is what makes the
// identity exact rather than modular; see below for why a truncating add is
// rejected outright.
//
// Derivation, at width W with a + b < 2**W:
//
//     a + b >= c  <=>  a + b + ~c + 1 >= 2**W          (~c = 2**W-1 - c)
//                 <=>  s + d + 1 >= 2**W               (a + b + ~c = s + d)
//                 <=>  s >= 2**W-1 - d = ~d
//
// and the strict form drops the +1, which turns >= into >. The other two
// relations are these two inverted, and a sum on the comparator's right-hand
// side is the mirror image, so all four ordering cell types are handled by
// choosing a relation and an inversion.
//
// Equality comes off the same pair: a + b == c iff a + b + ~c == 2**W-1, i.e.
// s + d == 2**W-1, and two values summing to all-ones can share no set bit (it
// would carry and clear one), so that is exactly s == ~d.
//
// A whole tree of adds collapses into one comparison the same way, since
// run_csa() reduces n summands to the two the identity expects. Only a child
// add its parent solely reads is absorbed, so every adder the walk takes in is
// dead afterwards.
//
// Soundness conditions, all structural:
//
//   1. No truncation. The comparator must see the mathematical sum, so the
//      add's Y must be at least max(|a|,|b|) + 1 bits and the comparator must
//      read all of it. An add that wraps compares its residue, which the
//      carry-save form does not reproduce.
//
//   2. Unsigned. Both the add and the comparator must be unsigned; a signed
//      compare orders the same bits differently.
//
// $sub is deliberately not matched. No width condition makes an unsigned
// subtract exact the way one does an add: a - b wraps whenever a < b, and
// ruling that out needs a value range the pass cannot establish locally.
//
// Profitability. When the sum feeds nothing but this comparator the adder
// disappears, so the rewrite is a strict win in both area and depth and fires
// unconditionally. When the sum has other readers the adder stays and the
// carry-save level is added area, so that case needs -timing: it fires only
// where the comparator sits on the module's longest path in the shared
// unit-delay model, which is where trading ~2 gates per bit for a carry chain
// pays.
//
// Decode (-decode). A one-hot decode of a sum, `1 << (a + b + ...)`, is a bank
// of equality tests `sum == k`, one per output bit, so it fuses off the same
// pair. Here the arithmetic is modular: the shift amount is W bits, so the
// decode only ever sees the sum mod 2**W, and a + b == K (mod 2**W) iff
// s == ~d on W bits (same argument, with the carry out of the top column
// dropped on both sides). That is what lets a constant subtract through, and
// with it the split form const folding leaves behind, `{x[k-1:0], x[W-1:k] - c}`,
// which is x - (c << k).
//
// K is a constant per output, so each column's s and v take one of two forms
// and every output is an AND over columns of one of four shared signals: the
// adder and the decoder's own predecode collapse into one XOR level and an AND
// tree. Muxes between the sum and the shift are pushed below the decode (a
// constant arm becomes a constant one-hot), and so is a mux summand whose
// select arrives after its arms, which moves a late select from in front of
// the adder to the last level. It only fires where the banks arrive strictly
// earlier than the adders and shift they replace, more than one output is
// read, and no bank sums 1-bit terms (a popcount is already a compressor tree).
// Relation the rewrite emits for `sum <rel> other`; the other comparisons are
// these inverted.
enum class Rel { Ge, Gt, Eq };

inline bool is_cmp_type(IdString type)
{
	return type.in(ID($lt), ID($le), ID($gt), ID($ge), ID($eq), ID($ne));
}

struct OptAddCmpWorker : UnitDelayTiming
{
	pool<SigBit> output_bits;

	// Tunables (see Pass::execute).
	int min_width = 8;
	bool timing_guard = false;
	int slack_margin = 0;

	int fused_exclusive = 0, fused_shared = 0, fused_wide = 0;
	int skipped_slack = 0, skipped_narrow = 0;

	OptAddCmpWorker(Module *module) : UnitDelayTiming(module)
	{
		// Port bits are collected by wire, not by testing port_output on a
		// sigmap representative: `assign out = sum` merges the two wires and
		// the representative can be either one.
		for (auto wire : module->wires())
			if (wire->port_output)
				for (auto bit : sigmap(wire))
					output_bits.insert(bit);

		for (auto cell : module->cells())
			for (auto &conn : cell->connections()) {
				bool is_out = cell->output(conn.first);
				for (auto bit : sigmap(conn.second)) {
					if (bit.wire == nullptr)
						continue;
					if (!is_out)
						consumer_map[bit].push_back(cell);
					// A bit with more than one driver ends a path instead of
					// electing one of them.
					else if (!driver_map.count(bit))
						driver_map[bit] = cell;
					else if (driver_map.at(bit) != cell)
						driver_map[bit] = nullptr;
				}
			}
	}

	// The unsigned non-truncating $add whose Y makes up all of `operand`, else
	// null. Zero padding above Y is fine (a widened use of the sum); anything
	// narrower would compare a residue the carry-save form does not reproduce.
	Cell *sum_driver(const SigSpec &operand)
	{
		SigSpec sig = sigmap(operand);
		if (sig.empty() || sig[0].wire == nullptr)
			return nullptr;

		auto it = driver_map.find(sig[0]);
		Cell *add = it == driver_map.end() ? nullptr : it->second;
		if (add == nullptr || add->type != ID($add))
			return nullptr;
		if (add->getParam(ID::A_SIGNED).as_bool() || add->getParam(ID::B_SIGNED).as_bool())
			return nullptr;

		int wa = add->getParam(ID::A_WIDTH).as_int();
		int wb = add->getParam(ID::B_WIDTH).as_int();
		int wy = add->getParam(ID::Y_WIDTH).as_int();
		if (wy < std::max(wa, wb) + 1)
			return nullptr;

		SigSpec y = sigmap(add->getPort(ID::Y));
		if (GetSize(sig) < GetSize(y))
			return nullptr;
		for (int i = 0; i < GetSize(sig); i++) {
			if (i < GetSize(y)) {
				if (sig[i] != y[i])
					return nullptr;
			} else if (sig[i] != SigBit(State::S0)) {
				return nullptr;
			}
		}
		return add;
	}

	// Is `sig` read by anything other than `reader`?
	bool escapes(const SigSpec &sig, Cell *reader)
	{
		for (auto bit : sigmap(sig)) {
			if (bit.wire == nullptr)
				continue;
			if (output_bits.count(bit))
				return true;
			auto it = consumer_map.find(bit);
			if (it == consumer_map.end())
				continue;
			for (auto cons : it->second)
				if (cons != reader)
					return true;
		}
		return false;
	}

	// Flatten an add tree into its summands, descending into a child add only
	// when the parent is its sole reader, so every adder the walk absorbs dies.
	// A child that truncates is left as an operand: its wrapped result is a
	// different value from the exact sum of its own operands.
	void collect_operands(Cell *add, std::vector<SigSpec> &operands, pool<Cell *> &tree)
	{
		tree.insert(add);
		for (IdString port : {ID::A, ID::B}) {
			SigSpec operand = add->getPort(port);
			Cell *child = sum_driver(operand);
			if (child != nullptr && !tree.count(child) && !escapes(child->getPort(ID::Y), add) &&
					GetSize(tree) + 1 < max_summands)
				collect_operands(child, operands, tree);
			else
				operands.push_back(operand);
		}
	}

	// Absorbing one adder adds one summand, so the tree ends with tree+1 of them.
	// Past a handful the carry-save levels cost more than the adders they remove.
	static const int max_summands = 6;

	// Does anything but `cmp` read the sum? If not, the adder dies with it.
	bool sum_is_shared(Cell *add, Cell *cmp) { return escapes(add->getPort(ID::Y), cmp); }

	// One 3:2 carry-save level: x + y + z == sum + (carry << 1), exactly, as long
	// as the shift keeps the top carry bit. `run_csa` establishes that.
	void csa_level(Cell *cell, const SigSpec &x, const SigSpec &y, const SigSpec &z,
			SigSpec &sum, SigSpec &carry)
	{
		std::string src = cell_src(cell);
		int width = GetSize(x);
		SigSpec xxy = module->Xor(NEW_ID2_SUFFIX("addcmp_cx"), x, y, false, src);
		sum = module->Xor(NEW_ID2_SUFFIX("addcmp_cs"), xxy, z, false, src);
		SigSpec c = module->Or(NEW_ID2_SUFFIX("addcmp_cv"),
		                       module->And(NEW_ID2_SUFFIX("addcmp_cxy"), x, y, false, src),
		                       module->And(NEW_ID2_SUFFIX("addcmp_cxz"), xxy, z, false, src),
		                       false, src);
		carry = SigSpec(State::S0);
		carry.append(c.extract(0, width - 1));
	}

	// Reduce n >= 3 operands to the two that sum to the same value, so the
	// comparator identity below sees its usual pair.
	//
	// Everything runs at width W = max(|o_i|) + ceil(log2 n), which makes the
	// total T = sum(o_i) < 2**W. Every level replaces x, y, z with s and 2c
	// where s + 2c == x + y + z, so the multiset total stays T; since the values
	// are non-negative and sum to T < 2**W, each one is itself below 2**W, so
	// 2c < 2**W and the shift never drops a set bit. That is what keeps the
	// reduction exact instead of modular.
	void run_csa(Cell *cell, std::vector<SigSpec> operands, SigSpec &s, SigSpec &d)
	{
		int width = 0;
		for (auto &o : operands)
			width = std::max(width, GetSize(o));
		width += log2p1_int(GetSize(operands) - 1); // ceil(log2 n) for n >= 2
		for (auto &o : operands)
			o.extend_u0(width, false);

		while (GetSize(operands) > 2) {
			SigSpec x = operands.back(); operands.pop_back();
			SigSpec y = operands.back(); operands.pop_back();
			SigSpec z = operands.back(); operands.pop_back();
			SigSpec sum, carry;
			csa_level(cell, x, y, z, sum, carry);
			operands.push_back(sum);
			operands.push_back(carry);
		}
		s = operands[0];
		d = operands[1];
	}

	// (a + b) >= c, or the strict form: one carry-save level plus one compare.
	// `cell` is the comparator being replaced; NEW_ID2_SUFFIX names after it.
	SigSpec emit_fused(Cell *cell, SigSpec a, SigSpec b, SigSpec c, Rel rel)
	{
		int width = std::max({GetSize(a), GetSize(b), GetSize(c)}) + 1;
		a.extend_u0(width, false);
		b.extend_u0(width, false);
		c.extend_u0(width, false);
		std::string src = cell_src(cell);

		SigSpec nc = module->Not(NEW_ID2_SUFFIX("addcmp_nc"), c, false, src);
		SigSpec axb = module->Xor(NEW_ID2_SUFFIX("addcmp_axb"), a, b, false, src);
		SigSpec sum = module->Xor(NEW_ID2_SUFFIX("addcmp_s"), axb, nc, false, src);
		SigSpec carry = module->Or(NEW_ID2_SUFFIX("addcmp_v"),
		                           module->And(NEW_ID2_SUFFIX("addcmp_ab"), a, b, false, src),
		                           module->And(NEW_ID2_SUFFIX("addcmp_xc"), axb, nc, false, src),
		                           false, src);

		// ~(carry << 1), spelled directly: the shifted-in zero inverts to one,
		// and the top carry bit is provably zero because a and b were widened.
		SigSpec ncarry(State::S1);
		ncarry.append(module->Not(NEW_ID2_SUFFIX("addcmp_nv"),
		                          carry.extract(0, width - 1), false, src));

		// Equality needs no ordering: sum + d == 2**W-1 holds only when the two
		// are bit-complements, since a shared set bit would carry and clear one.
		if (rel == Rel::Eq)
			return module->Eq(NEW_ID2_SUFFIX("addcmp_eq"), sum, ncarry, false, src);
		return rel == Rel::Gt ? module->Gt(NEW_ID2_SUFFIX("addcmp_gt"), sum, ncarry, false, src)
		                      : module->Ge(NEW_ID2_SUFFIX("addcmp_ge"), sum, ncarry, false, src);
	}

	void fuse(Cell *cell, const std::vector<SigSpec> &operands, bool sum_on_a)
	{
		// Relation to emit for `sum <rel> other`, and whether to invert it.
		// With the sum on the right the comparison is read backwards, which
		// swaps >= against > and flips the inversion with it; equality reads the
		// same either way.
		IdString t = cell->type;
		Rel rel = t.in(ID($eq), ID($ne)) ? Rel::Eq
		        : (sum_on_a ? t.in(ID($gt), ID($le)) : t.in(ID($lt), ID($ge))) ? Rel::Gt
		        : Rel::Ge;
		bool invert = t == ID($ne) ||
				(sum_on_a ? t.in(ID($lt), ID($le)) : t.in(ID($gt), ID($ge)));

		// More than two summands reduce to two first, which is the pair the
		// identity below expects
		SigSpec a = operands[0], b = operands[1];
		if (GetSize(operands) > 2)
			run_csa(cell, operands, a, b);

		SigSpec other = cell->getPort(sum_on_a ? ID::B : ID::A);
		SigSpec y = emit_fused(cell, a, b, other, rel);
		if (invert)
			y = module->Not(NEW_ID2_SUFFIX("addcmp_inv"), y, false, cell_src(cell));

		SigSpec cmp_y = cell->getPort(ID::Y);
		y.extend_u0(GetSize(cmp_y), false);
		module->remove(cell);
		module->connect(cmp_y, y);
	}

	int run()
	{
		std::vector<std::tuple<Cell *, std::vector<SigSpec>, bool>> hits;
		for (auto cmp : module->selected_cells()) {
			if (!is_cmp_type(cmp->type))
				continue;
			if (cmp->getParam(ID::A_SIGNED).as_bool() || cmp->getParam(ID::B_SIGNED).as_bool())
				continue;

			for (int side = 0; side < 2; side++) {
				bool sum_on_a = side == 0;
				Cell *add = sum_driver(cmp->getPort(sum_on_a ? ID::A : ID::B));
				if (add == nullptr)
					continue;

				// A narrow adder is cheaper than the carry-save level plus the
				// wider compare it would leave behind, and the boolean mapper
				// flattens it anyway.
				if (add->getParam(ID::Y_WIDTH).as_int() < min_width) {
					skipped_narrow++;
					continue;
				}

				bool exclusive = !sum_is_shared(add, cmp);
				if (!exclusive) {
					if (!timing_guard)
						continue;
					int depth = path_depth(cmp->getPort(ID::Y));
					if (depth < longest_path() - slack_margin) {
						log_debug("  %s: off-critical (depth %d of %d)\n",
						          log_id(cmp), depth, longest_path());
						skipped_slack++;
						continue;
					}
				}

				std::vector<SigSpec> operands;
				pool<Cell *> tree;
				collect_operands(add, operands, tree);

				log_debug("  %s: fusing %s (%d summand(s) from %d add(s), %s)\n",
				          log_id(cmp), log_id(add), GetSize(operands), GetSize(tree),
				          exclusive ? "sole reader" : "critical");
				hits.emplace_back(cmp, operands, sum_on_a);
				(exclusive ? fused_exclusive : fused_shared)++;
				if (GetSize(operands) > 2)
					fused_wide++;
				break;
			}
		}

		for (auto &[cmp, operands, sum_on_a] : hits)
			fuse(cmp, operands, sum_on_a);

		if (skipped_narrow || skipped_slack)
			log_debug("  %s: skipped %d narrow adder(s), %d off-critical comparator(s).\n",
			          log_id(module), skipped_narrow, skipped_slack);
		return GetSize(hits);
	}

	// ------------------------------------------------------------------
	// -decode: `onehot << (sum)` as carry-save equality banks
	// ------------------------------------------------------------------

	// Bounds on one decode: amount bits, output bits, summands per equality
	// bank, distinct banks per shift, and how many muxes deep to push.
	static constexpr int max_decode_width = 12;
	static constexpr int max_decode_outputs = 256;
	static constexpr int max_decode_terms = 8;
	static constexpr int max_decode_leaves = 4;
	static constexpr int max_decode_mux_depth = 4;
	static constexpr int max_lin_depth = 8;

	int decoded = 0, decode_banks = 0, decode_muxes = 0;

	// A summand counted negatively when `neg`; all sigs are decode_width bits.
	struct Term { SigSpec sig; bool neg; };
	// sum(terms) + c, mod 2**decode_width.
	struct LinForm {
		std::vector<Term> terms;
		uint64_t c = 0;
	};
	// One node of the pushed decode: a mux over two child nodes, or a bank.
	struct DecodePlan {
		SigBit sel;
		int a = -1, b = -1; // children for sel = 0 / 1; -1 marks a bank
		LinForm lin;
	};

	int decode_width = 0;
	std::vector<DecodePlan> plans;
	int plan_banks = 0, plan_sums = 0, plan_muxes = 0;

	uint64_t wmask() const { return (1ull << decode_width) - 1; }

	Cell *driver(SigBit bit)
	{
		if (bit.wire == nullptr)
			return nullptr;
		auto it = driver_map.find(bit);
		return it == driver_map.end() ? nullptr : it->second;
	}

	// Is `sig` exactly the low bits of `cell`'s Y, zero-padded above it?
	bool reads_low_y(const SigSpec &sig, Cell *cell)
	{
		SigSpec y = sigmap(cell->getPort(ID::Y));
		for (int i = 0; i < GetSize(sig); i++)
			if (sig[i] != (i < GetSize(y) ? y[i] : SigBit(State::S0)))
				return false;
		return true;
	}

	// The $mux every non-constant bit of `sig` comes from, with its two arms
	// read at the same positions; null when the bits come from anywhere else.
	Cell *mux_arms(const SigSpec &sig, SigSpec &a, SigSpec &b)
	{
		Cell *mux = nullptr;
		a = b = SigSpec();
		for (auto bit : sigmap(sig)) {
			if (bit.wire == nullptr) {
				a.append(bit);
				b.append(bit);
				continue;
			}
			Cell *d = driver(bit);
			if (d == nullptr || d->type != ID($mux) || (mux != nullptr && d != mux))
				return nullptr;
			mux = d;
			SigSpec y = sigmap(mux->getPort(ID::Y));
			int idx = 0;
			while (y[idx] != bit)
				idx++;
			a.append(sigmap(mux->getPort(ID::A))[idx]);
			b.append(sigmap(mux->getPort(ID::B))[idx]);
		}
		return mux;
	}

	// Largest unsigned value of `sig`: its constant-zero top bits, tightened
	// through a non-wrapping unsigned add or a mux. A narrower add zero-padded
	// into the decode is the exact sum only if it cannot wrap, and widths alone
	// cannot show that for a chain (6-bit + 3-bit into 6 bits fits when the
	// 6-bit side is itself 5-bit + 4-bit).
	uint64_t upper_bound(SigSpec sig, int depth = 4)
	{
		sig = sigmap(sig);
		int top = GetSize(sig) - 1;
		while (top >= 0 && sig[top] == State::S0)
			top--;
		if (top < 0)
			return 0;
		if (top >= 30)
			return ~0ull >> 2; // past what any decode here can use
		sig = sig.extract(0, top + 1);
		if (sig.is_fully_def())
			return sig.as_const().as_int();
		uint64_t bound = (1ull << (top + 1)) - 1;
		Cell *d = driver(sig[0]);
		if (depth <= 0 || d == nullptr)
			return bound;
		SigSpec a, b;
		if (d->type == ID($add) && !d->getParam(ID::A_SIGNED).as_bool() &&
				!d->getParam(ID::B_SIGNED).as_bool() && reads_low_y(sig, d) &&
				GetSize(sig) == d->getParam(ID::Y_WIDTH).as_int()) {
			a = d->getPort(ID::A);
			b = d->getPort(ID::B);
			a.extend_u0(GetSize(sig));
			b.extend_u0(GetSize(sig));
			uint64_t sum = upper_bound(a, depth - 1) + upper_bound(b, depth - 1);
			return std::min(bound, sum);
		}
		if (mux_arms(sig, a, b) != nullptr)
			return std::min(bound, std::max(upper_bound(a, depth - 1), upper_bound(b, depth - 1)));
		return bound;
	}

	// Operand `port` of `arith` as it reaches a decode_width-bit sum: extended
	// the way the cell extends it to its own Y, then cut or zero-padded to W.
	SigSpec arith_operand(Cell *arith, IdString port)
	{
		int yw = arith->getParam(ID::Y_WIDTH).as_int();
		bool is_signed = arith->type == ID($neg) ? arith->getParam(ID::A_SIGNED).as_bool()
			: arith->getParam(ID::A_SIGNED).as_bool() && arith->getParam(ID::B_SIGNED).as_bool();
		SigSpec sig = arith->getPort(port);
		sig.extend_u0(yw, is_signed);
		sig.extend_u0(decode_width, false);
		return sig;
	}

	// Open `sig` as a $add/$sub/$neg whose result reaches the decode exactly
	// mod 2**W: either Y is at least W bits, or it is a narrower unsigned add
	// that provably cannot wrap. Null otherwise.
	Cell *arith_driver(const SigSpec &sig)
	{
		Cell *d = driver(sig[0]);
		if (d == nullptr || !d->type.in(ID($add), ID($sub), ID($neg)) || !reads_low_y(sig, d))
			return nullptr;
		int yw = d->getParam(ID::Y_WIDTH).as_int();
		if (yw >= decode_width)
			return d;
		if (d->type != ID($add) || d->getParam(ID::A_SIGNED).as_bool() || d->getParam(ID::B_SIGNED).as_bool())
			return nullptr;
		SigSpec a = d->getPort(ID::A), b = d->getPort(ID::B);
		a.extend_u0(yw);
		b.extend_u0(yw);
		return upper_bound(a) + upper_bound(b) < (1ull << yw) ? d : nullptr;
	}

	// `{x[k-1:0], (x[W-1:k] + c) mod 2**(W-k)}`: a constant added to the top
	// of a value only, which is how const folding splits a subtract of a
	// multiple of 2**k. It is x + (c << k) mod 2**W, so open it as that.
	bool lin_split(const SigSpec &sig, bool neg, LinForm &L, int depth)
	{
		int W = decode_width;
		Cell *top = driver(sig[W - 1]);
		if (top == nullptr || !top->type.in(ID($add), ID($sub)))
			return false;
		SigSpec y = sigmap(top->getPort(ID::Y));
		int k = 0;
		while (k < W && sig[k] != y[0])
			k++;
		if (k == 0 || k >= W || GetSize(y) < W - k || sig.extract(k, W - k) != y.extract(0, W - k))
			return false;

		// One operand constant; a $sub only with the constant subtracted
		bool b_const = top->getPort(ID::B).is_fully_def();
		bool a_const = top->type == ID($add) && top->getPort(ID::A).is_fully_def();
		if (!a_const && !b_const)
			return false;
		int yw = GetSize(y);
		bool is_signed = top->getParam(ID::A_SIGNED).as_bool() && top->getParam(ID::B_SIGNED).as_bool();
		SigSpec var = top->getPort(b_const ? ID::A : ID::B), con = top->getPort(b_const ? ID::B : ID::A);
		var.extend_u0(yw, is_signed);
		con.extend_u0(yw, is_signed);
		uint64_t cv = uint64_t(con.extract(0, W - k).as_const().as_int()) << k;
		if (top->type == ID($sub))
			cv = 0 - cv;
		L.c = (neg ? L.c - cv : L.c + cv) & wmask();

		SigSpec x = sig.extract(0, k);
		x.append(sigmap(var.extract(0, W - k)));
		lin_add(x, neg, L, depth - 1);
		return true;
	}

	// Accumulate W-bit `sig` into L, negated when `neg`. Adds and subtracts are
	// opened while the result stays exact mod 2**W; anything else is a summand.
	void lin_add(SigSpec sig, bool neg, LinForm &L, int depth)
	{
		sig = sigmap(sig);
		if (sig.is_fully_def()) {
			uint64_t v = uint64_t(sig.as_const().as_int()) & wmask();
			L.c = (neg ? L.c - v : L.c + v) & wmask();
			return;
		}
		if (depth > 0 && GetSize(L.terms) + 1 < max_decode_terms) {
			if (Cell *d = arith_driver(sig)) {
				lin_add(arith_operand(d, ID::A), d->type == ID($neg) ? !neg : neg, L, depth - 1);
				if (d->type != ID($neg))
					lin_add(arith_operand(d, ID::B), d->type == ID($sub) ? !neg : neg, L, depth - 1);
				return;
			}
			if (lin_split(sig, neg, L, depth))
				return;
		}
		L.terms.push_back({sig, neg});
	}

	int add_plan(DecodePlan plan)
	{
		plans.push_back(plan);
		return GetSize(plans) - 1;
	}

	int add_mux_plan(SigSpec sel, int a, int b)
	{
		if (a < 0 || b < 0)
			return -1;
		DecodePlan plan;
		plan.sel = sigmap(sel)[0];
		plan.a = a;
		plan.b = b;
		plan_muxes++;
		return add_plan(plan);
	}

	// A bank for L, after distributing a summand that is a mux whose select
	// arrives after its arms: with the mux below the decode that select is the
	// last level instead of an operand ahead of every column. Only the mux's own
	// arms are weighed, not the other summands: the unit model overcharges a
	// casez encoder feeding the bank (a $pmux of wide $eq) well past a carry
	// chain the mapped netlist finds slower.
	int plan_lin(const LinForm &L, int depth)
	{
		for (int i = 0; depth > 0 && i < GetSize(L.terms); i++) {
			SigSpec a, b;
			Cell *mux = mux_arms(L.terms[i].sig, a, b);
			if (mux == nullptr || arrival(mux->getPort(ID::S)) <= std::max(arrival(a), arrival(b)))
				continue;
			LinForm la = L, lb = L;
			la.terms.erase(la.terms.begin() + i);
			lb.terms.erase(lb.terms.begin() + i);
			lin_add(a, L.terms[i].neg, la, max_lin_depth);
			lin_add(b, L.terms[i].neg, lb, max_lin_depth);

			// A push that runs out of banks is undone and the summand banked as is
			int saved_plans = GetSize(plans), saved_banks = plan_banks;
			int saved_sums = plan_sums, saved_muxes = plan_muxes;
			int pa = plan_lin(la, depth - 1);
			int pb = pa < 0 ? -1 : plan_lin(lb, depth - 1);
			int root = add_mux_plan(mux->getPort(ID::S), pa, pb);
			if (root >= 0)
				return root;
			plans.resize(saved_plans);
			plan_banks = saved_banks;
			plan_sums = saved_sums;
			plan_muxes = saved_muxes;
		}
		// lin_add checks the cap before opening an add, not after its operands
		// land, so a deep chain can still overshoot it by the chain's depth
		if (GetSize(L.terms) > max_decode_terms)
			return -1;
		if (!L.terms.empty() && ++plan_banks > max_decode_leaves)
			return -1;
		if (GetSize(L.terms) >= 2)
			plan_sums++;
		DecodePlan plan;
		plan.lin = L;
		return add_plan(plan);
	}

	// Push the decode through the muxes that choose the amount, then bank it.
	int plan_amount(const SigSpec &amt, int depth)
	{
		SigSpec a, b;
		Cell *mux = depth > 0 ? mux_arms(amt, a, b) : nullptr;
		if (mux != nullptr) {
			int pa = plan_amount(a, depth - 1);
			int pb = pa < 0 ? -1 : plan_amount(b, depth - 1);
			return add_mux_plan(mux->getPort(ID::S), pa, pb);
		}
		LinForm L;
		lin_add(amt, false, L, max_lin_depth);
		return plan_lin(L, depth);
	}

	// Carry-save levels take the three earliest summands first; emit_bank
	// reduces in the same order, so both agree on where the latest one joins.
	static void csa_schedule(std::vector<int> &ts)
	{
		std::sort(ts.begin(), ts.end());
		while (GetSize(ts) > 2) {
			int t = std::max({ts[0], ts[1], ts[2]}) + 2;
			ts.erase(ts.begin(), ts.begin() + 3);
			ts.insert(std::upper_bound(ts.begin(), ts.end(), t), 2, t);
		}
	}

	// Unit-delay arrival of a planned node, in the currency of the shift it
	// replaces: a bank costs its carry-save levels, the XOR against the column
	// below and the AND tree; a pushed mux one level.
	int plan_arrival(int idx)
	{
		const DecodePlan &plan = plans[idx];
		if (plan.a >= 0)
			return std::max({arrival(SigSpec(plan.sel)), plan_arrival(plan.a), plan_arrival(plan.b)}) + 1;
		std::vector<int> ts;
		for (auto &t : plan.lin.terms)
			ts.push_back(arrival(t.sig));
		if (ts.empty())
			return 0;
		csa_schedule(ts);
		int xy = GetSize(ts) == 1 ? ts[0] : std::max(ts[0], ts[1]) + 2;
		return xy + log2p1_int(decode_width);
	}

	// Does anything use `bit`, looking through bitwise cells to the bit each one
	// passes it on as? A wide mux behind the shift that feeds only its bit 0
	// onward leaves every other decoder output dead.
	bool bit_live(SigBit bit, int depth)
	{
		if (output_bits.count(bit))
			return true;
		auto it = consumer_map.find(bit);
		if (it == consumer_map.end())
			return false;
		for (Cell *c : it->second) {
			if (depth <= 0 || !c->type.in(ID($mux), ID($and), ID($or), ID($xor), ID($xnor), ID($not), ID($pos)))
				return true;
			if (c->type == ID($mux) && sigmap(c->getPort(ID::S))[0] == bit)
				return true;
			SigSpec y = sigmap(c->getPort(ID::Y));
			for (IdString port : {ID::A, ID::B}) {
				if (!c->hasPort(port))
					continue;
				SigSpec in = sigmap(c->getPort(port));
				for (int i = 0; i < std::min(GetSize(in), GetSize(y)); i++)
					if (in[i] == bit && bit_live(y[i], depth - 1))
						return true;
			}
		}
		return false;
	}

	// `out[k] = (sum(L) == k - pos)` for every output bit of the shift.
	SigSpec emit_bank(Cell *cell, LinForm L, int out_width, int pos)
	{
		int W = decode_width;
		std::string src = cell_src(cell);

		// A negated summand is its complement plus one, mod 2**W
		std::vector<std::pair<int, SigSpec>> ops;
		for (auto &t : L.terms) {
			SigSpec sig = t.sig;
			if (t.neg) {
				sig = module->Not(NEW_ID2_SUFFIX("adddec_neg"), sig, false, src);
				L.c = (L.c + 1) & wmask();
			}
			ops.emplace_back(arrival(t.sig), sig);
		}
		auto target = [&](int k) { return (uint64_t(k - pos) - L.c) & wmask(); };
		auto reachable = [&](int k) { return k >= pos && uint64_t(k - pos) <= wmask(); };

		SigSpec out;
		if (GetSize(ops) <= 1) {
			for (int k = 0; k < out_width; k++) {
				if (!reachable(k))
					out.append(State::S0);
				else if (ops.empty())
					out.append(target(k) == 0 ? State::S1 : State::S0);
				else
					out.append(module->Eq(NEW_ID2_SUFFIX("adddec_eq"), ops[0].second,
					                      Const(int(target(k)), W), false, src));
			}
			return out;
		}

		// Reduce to two in csa_schedule's order, so the latest summand joins last
		std::stable_sort(ops.begin(), ops.end(),
		                 [](const auto &x, const auto &y) { return x.first < y.first; });
		while (GetSize(ops) > 2) {
			SigSpec sum, carry;
			csa_level(cell, ops[0].second, ops[1].second, ops[2].second, sum, carry);
			int t = std::max({ops[0].first, ops[1].first, ops[2].first}) + 2;
			ops.erase(ops.begin(), ops.begin() + 3);
			auto at = std::find_if(ops.begin(), ops.end(), [&](const auto &o) { return o.first > t; });
			at = ops.insert(at, {t, carry});
			ops.insert(at, {t, sum});
		}
		SigSpec x = ops[0].second, y = ops[1].second;

		// Column i passes when s_i ^ v_{i-1} = 1 (s_0 alone for i = 0), with
		// s_i = x_i ^ y_i ^ ~K_i and v_i = maj(x_i, y_i, ~K_i). K_i picks the
		// form: s is xy or ~xy, v is x & y or x | y.
		SigSpec xy = module->Xor(NEW_ID2_SUFFIX("adddec_xy"), x, y, false, src);
		SigSpec nxy = module->Not(NEW_ID2_SUFFIX("adddec_nxy"), xy, false, src);
		SigSpec pass_g, pass_o, fail_g, fail_o; // column 1..W-1, K_i = 1 / K_i = 0
		if (W > 1) {
			SigSpec hi = xy.extract(1, W - 1);
			SigSpec g = module->And(NEW_ID2_SUFFIX("adddec_g"), x.extract(0, W - 1), y.extract(0, W - 1), false, src);
			SigSpec o = module->Or(NEW_ID2_SUFFIX("adddec_o"), x.extract(0, W - 1), y.extract(0, W - 1), false, src);
			pass_g = module->Xor(NEW_ID2_SUFFIX("adddec_tg"), hi, g, false, src);
			pass_o = module->Xor(NEW_ID2_SUFFIX("adddec_to"), hi, o, false, src);
			fail_g = module->Not(NEW_ID2_SUFFIX("adddec_ng"), pass_g, false, src);
			fail_o = module->Not(NEW_ID2_SUFFIX("adddec_no"), pass_o, false, src);
		}
		for (int k = 0; k < out_width; k++) {
			if (!reachable(k)) {
				out.append(State::S0);
				continue;
			}
			uint64_t K = target(k);
			SigSpec cols = (K & 1) ? xy[0] : nxy[0];
			for (int i = 1; i < W; i++) {
				bool ki = (K >> i) & 1, kp = (K >> (i - 1)) & 1;
				cols.append((ki ? (kp ? pass_g : pass_o) : (kp ? fail_g : fail_o))[i - 1]);
			}
			out.append(module->ReduceAnd(NEW_ID2_SUFFIX("adddec_and"), cols, false, src));
		}
		return out;
	}

	SigSpec emit_plan(Cell *cell, int idx, int out_width, int pos,
	                  std::map<std::pair<std::vector<std::pair<SigSpec, bool>>, uint64_t>, SigSpec> &banks)
	{
		const DecodePlan &plan = plans[idx];
		if (plan.a >= 0) {
			SigSpec a = emit_plan(cell, plan.a, out_width, pos, banks);
			SigSpec b = emit_plan(cell, plan.b, out_width, pos, banks);
			return module->Mux(NEW_ID2_SUFFIX("adddec_mux"), a, b, plan.sel, cell_src(cell));
		}
		// Arms that reach the same sum share one bank
		std::vector<std::pair<SigSpec, bool>> key;
		for (auto &t : plan.lin.terms)
			key.emplace_back(t.sig, t.neg);
		std::sort(key.begin(), key.end());
		auto it = banks.find({key, plan.lin.c});
		if (it != banks.end())
			return it->second;
		if (GetSize(key) >= 2)
			decode_banks++;
		return banks[{key, plan.lin.c}] = emit_bank(cell, plan.lin, out_width, pos);
	}

	int run_decode()
	{
		// Plan every shift against the untouched netlist first: the index is not
		// updated as cells are emitted, so a removed shift must not be walked
		struct Hit { Cell *cell; std::vector<DecodePlan> plans; int root, pos, width, muxes; };
		std::vector<Hit> hits;
		for (auto cell : module->selected_cells()) {
			if (cell->type != ID($shl))
				continue;
			// A constant with exactly one set bit, as the shift sees it
			SigSpec a = cell->getPort(ID::A);
			int out_width = GetSize(cell->getPort(ID::Y));
			a.extend_u0(out_width, cell->getParam(ID::A_SIGNED).as_bool());
			if (!a.is_fully_def())
				continue;
			int pos = -1, ones = 0;
			for (int i = 0; i < out_width; i++)
				if (a[i] == State::S1) {
					pos = i;
					ones++;
				}
			SigSpec amt = sigmap(cell->getPort(ID::B));
			if (ones != 1 || GetSize(amt) > max_decode_width || out_width > max_decode_outputs)
				continue;

			// One live output is a single `sum == k`: the $eq fusion above owns
			// that, behind -min-width, and banking it only adds fanout to the sum
			int live = 0;
			for (auto bit : sigmap(cell->getPort(ID::Y)))
				live += bit_live(bit, max_decode_mux_depth);
			if (live < 2)
				continue;

			// Only a critical decode: pushed muxes duplicate it, and an adder
			// the sum shares with other readers stays
			int depth = path_depth(cell->getPort(ID::Y));
			if (depth < longest_path() - slack_margin) {
				log_debug("  %s: off-critical decode (depth %d of %d)\n", log_id(cell), depth, longest_path());
				continue;
			}

			decode_width = GetSize(amt);
			plans.clear();
			plan_banks = plan_sums = plan_muxes = 0;
			int root = plan_amount(amt, max_decode_mux_depth);
			if (root < 0 || plan_sums == 0) {
				log_debug("  %s: no sum to fuse (%d bank(s))\n", log_id(cell), plan_banks);
				continue;
			}

			// A bank of 1-bit summands is a popcount, which the compressor tree
			// already maps as well as carry-save levels would
			if (std::any_of(plans.begin(), plans.end(), [&](const DecodePlan &p) {
				    return p.a < 0 && GetSize(p.lin.terms) >= 2 &&
				           std::any_of(p.lin.terms.begin(), p.lin.terms.end(),
				                       [&](const Term &t) { return upper_bound(t.sig) <= 1; });
			    })) {
				log_debug("  %s: popcount summands\n", log_id(cell));
				continue;
			}

			// The banks must beat the adders and shift they replace. Both end in an
			// AND over W columns, so charge the shift that tree rather than the
			// unit model's log2 of its output width: the question is only whether
			// carry-save levels and two XORs beat the carry chain. A popcount is
			// already a compressor tree, and decoding it this way only adds levels.
			int old_t = arrival(amt) + log2p1_int(decode_width), new_t = plan_arrival(root);
			if (new_t >= old_t) {
				log_debug("  %s: decode not shallower (%d vs %d levels)\n", log_id(cell), new_t, old_t);
				continue;
			}
			log_debug("  %s: decode at %d levels against %d\n", log_id(cell), new_t, old_t);

			hits.push_back({cell, plans, root, pos, decode_width, plan_muxes});
		}

		std::vector<std::pair<Cell *, SigSpec>> done;
		for (auto &hit : hits) {
			plans = hit.plans;
			decode_width = hit.width;
			std::map<std::pair<std::vector<std::pair<SigSpec, bool>>, uint64_t>, SigSpec> banks;
			int before = decode_banks;
			SigSpec y = emit_plan(hit.cell, hit.root, GetSize(hit.cell->getPort(ID::Y)), hit.pos, banks);
			log("  %s: %s decoded as %d carry-save equality bank(s) below %d mux(es)\n",
			    log_id(module), log_id(hit.cell), decode_banks - before, hit.muxes);
			decode_muxes += hit.muxes;
			done.emplace_back(hit.cell, y);
		}
		for (auto &[cell, y] : done) {
			SigSpec shl_y = cell->getPort(ID::Y);
			module->remove(cell);
			module->connect(shl_y, y);
		}
		decoded += GetSize(done);
		return GetSize(done);
	}
};

struct OptAddCmpPass : public Pass {
	OptAddCmpPass() : Pass("opt_addcmp", "fuse an adder into the comparator it feeds") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_addcmp [options] [selection]\n");
		log("\n");
		log("Replace a comparison against a sum with a carry-save comparison, so the\n");
		log("adder no longer sits between its own operands and the comparator:\n");
		log("\n");
		log("    (a + b) >= c    ->    s >= ~(v << 1)      s = a ^ b ^ ~c\n");
		log("    (a + b) >  c    ->    s >  ~(v << 1)      v = maj(a, b, ~c)\n");
		log("\n");
		log("Bound checks (address range, credit, overflow) ask for the order of a sum\n");
		log("and never for the sum itself, but the RTL spells them as an adder feeding\n");
		log("a comparator, which puts a full carry-propagate network ahead of the\n");
		log("comparator's own. One carry-save level replaces it: the operands are\n");
		log("reduced to a sum and a carry vector in constant depth, and the single\n");
		log("remaining carry chain is the comparator's.\n");
		log("\n");
		log("Operands are first widened to max(|a|,|b|,|c|) + 1 bits. That makes the\n");
		log("identity exact -- the carry out of the top column is maj(0, 0, x) = 0, so\n");
		log("the shift drops nothing -- and it is why an add whose result is narrower\n");
		log("than its operands (comparing a residue) is rejected instead. The other\n");
		log("two relations are these two inverted, and a sum on the comparator's\n");
		log("right-hand side is the mirror image, so all four orderings are handled.\n");
		log("\n");
		log("$eq and $ne fuse off the same pair, since a sum and a carry vector adding\n");
		log("to all-ones must be bit-complements. A tree of adds is flattened into one\n");
		log("carry-save reduction, absorbing only child adders their parent solely\n");
		log("reads so that each one absorbed is dead afterwards.\n");
		log("\n");
		log("Signed adds and signed comparisons are rejected: the carry-save identity\n");
		log("is an unsigned one. $sub is rejected too -- an unsigned subtract wraps\n");
		log("whenever a < b, which no width condition rules out.\n");
		log("\n");
		log("When the comparator is the sum's only reader the adder is dead after the\n");
		log("rewrite, so the fusion is a strict win and always taken. When the sum has\n");
		log("other readers the adder stays and the carry-save level is added area,\n");
		log("which only pays on a critical comparator -- that case needs -timing.\n");
		log("\n");
		log("    -timing\n");
		log("        also fuse when the sum has other readers, provided the comparator\n");
		log("        lies on the module's longest unit-delay path.\n");
		log("\n");
		log("    -slack-margin <int>\n");
		log("        levels below the module depth still counted as critical for\n");
		log("        -timing (default: 0)\n");
		log("\n");
		log("    -min-width <n>\n");
		log("        skip adders narrower than this many result bits (default: 8).\n");
		log("        Below it the adder is cheaper than the logic that would replace\n");
		log("        it, and the boolean mapper flattens it regardless.\n");
		log("\n");
		log("    -decode\n");
		log("        also rewrite a one-hot decode of a sum, `onehot << (a + b + ...)`,\n");
		log("        as a bank of carry-save equality tests, one per output bit. The\n");
		log("        amount is W bits, so the identity is taken mod 2**W, which admits\n");
		log("        subtracts and the split `{x[k-1:0], x[W-1:k] - c}` form. Every\n");
		log("        output shares four per-column signals, so the adder and the\n");
		log("        decoder's predecode become one XOR level and an AND tree. Muxes\n");
		log("        choosing the amount are pushed below the decode, as is a mux\n");
		log("        summand whose select arrives after its arms. Only a shift on the\n");
		log("        module's longest unit-delay path (within -slack-margin) is\n");
		log("        rewritten, only when some arm really is a sum, and only when the\n");
		log("        banks arrive strictly earlier than the adders and shift they\n");
		log("        replace; adders are not width-gated here. Off by default.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_ADDCMP pass (fuse adder into comparator).\n");

		int min_width = 8, slack_margin = 0;
		bool timing_guard = false, decode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-timing") {
				timing_guard = true;
				continue;
			}
			if (args[argidx] == "-decode") {
				decode = true;
				continue;
			}
			if (args[argidx] == "-slack-margin" && argidx + 1 < args.size()) {
				slack_margin = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-min-width" && argidx + 1 < args.size()) {
				min_width = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total = 0, exclusive = 0, wide = 0, decoded = 0, banks = 0, muxes = 0;
		for (auto module : design->selected_modules()) {
			// The worker indexes every bit in the module, so check there is
			// something to match before paying for it
			bool has_cmp = false, has_shl = false;
			for (auto cell : module->selected_cells()) {
				has_cmp |= is_cmp_type(cell->type);
				has_shl |= decode && cell->type == ID($shl) && cell->getPort(ID::A).is_fully_def();
			}

			if (has_cmp) {
				OptAddCmpWorker worker(module);
				worker.min_width = min_width;
				worker.timing_guard = timing_guard;
				worker.slack_margin = slack_margin;
				total += worker.run();
				exclusive += worker.fused_exclusive;
				wide += worker.fused_wide;
			}

			// Fresh index: the compare fusion above has rewritten the netlist
			if (has_shl) {
				OptAddCmpWorker worker(module);
				worker.slack_margin = slack_margin;
				decoded += worker.run_decode();
				banks += worker.decode_banks;
				muxes += worker.decode_muxes;
			}
		}

		if (total || decoded)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Fused %d add-compare region(s); %d left the adder dead, %d flattened "
		    "more than two summands.\n", total, exclusive, wide);
		if (decode)
			log("Decoded %d shift(s) of a sum as %d carry-save equality bank(s) below "
			    "%d pushed mux(es).\n", decoded, banks, muxes);
	}
} OptAddCmpPass;

PRIVATE_NAMESPACE_END
