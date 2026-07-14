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
 *
 */

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/consteval.h"
#include <algorithm>
#include <cctype>
#include <map>
#include <queue>
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Pack a per-lane integer vector into a Const with elem_w bits per lane,
// lane-major (lane k occupies bits [k*elem_w +: elem_w]).
static Const pack_lanes(const vector<int> &vals, int elem_w)
{
	// Lane values come from the small field widths above (<= max_attr_w), so a
	// 32-bit int always holds them. Assert rather than silently truncating, and
	// keep b < 32 so we never shift an int by >= its width (undefined behaviour).
	log_assert(elem_w < 32);
	vector<State> bits(vals.size() * elem_w, State::S0);
	for (int k = 0; k < GetSize(vals); k++)
		for (int b = 0; b < elem_w; b++)
			if ((vals[k] >> b) & 1)
				bits[k * elem_w + b] = State::S1;
	return Const(bits);
}

#include "passes/opt/cut_region.h"

struct OptFirstFitAllocWorker : CutRegionWorker {
	int min_n = 4;
	int max_n = 64;
	int max_field_w = 6;   // max index (dsel) element width
	int max_cat_w = 6;     // max category width c
	int max_attr_w = 8;    // max per-lane attr width for the xbar field gather
	int max_gather_w = 31; // max per-slot width for the exclusive identity gather
	                       // (pack_lanes packs each lane into < 32 bits)
	int max_gather_cands = 8; // cap the exclusive identity-gather candidate sweep
	// Thermometer exclusive scan is O(n log n * nb^2); keep nb small so emit
	// stays cheap for max_n=64. Larger budgets fall back to binary sat-log.
	int max_therm_nb = 8;
	// Cap xbar emit size: n lanes * nb slots * slot_w bits of $pmux cases, plus
	// n parallel $bmux tables of 2^a entries. Skip the gather (keep dsel) when
	// the product would explode compile/techmap cost.
	int64_t max_xbar_emit_bits = 1 << 18; // 256K bit-cases (~N=64, nb=32, slot_w=128)

	// ---- gather-rooted anchor ----
	// Detect an exclusive first-fit that is consumed only as a per-slot data
	// gather (slot_data[s] = data[the s-th enabled lane]) with no explicit
	// per-lane rank/dsel bus, optionally buried under guard muxes (an FSM
	// `case`, a per-entry `hit` mux) and/or with entry-side compaction (the
	// s-th non-guarded slot reads the s-th enabled lane). Correctness is
	// gated by the same ConstEval fingerprint used by the dsel path.
	bool gather_root = true;
	int max_gather_roots = 32; // per-module cap on gather-root candidates
	int max_gather_en = 24;    // per-root cap on enable-bus candidates
	int max_sel_cands = 8;     // per-root cap on entry-select-bus candidates
	bool dbg_compact = false;  // verbose compaction cut/group diagnostics
	int min_slots = 2;         // min gather slot count (== exclusive nb)
	int max_guard_peel = 8;    // max guard-mux levels to descend when peeling

	int regions_rewritten = 0;
	int cells_added = 0;

	OptFirstFitAllocWorker(Module *module) : CutRegionWorker(module) {}

	// ----------------------------------------------------------------
	// Reference closed-form semantics of the greedy first-fit allocator.
	//
	// Lanes are processed in priority order (LSB-first here; the caller
	// reverses for MSB-first). A "leader" is the first enabled lane of each
	// category that is reached before its category's slot is taken; broadcast
	// (bc) lanes after the first leader are suppressed. Leaders take slots
	// 0,1,2,... in order; the per-lane rank (dsel) is the slot of the leader
	// matching that lane's category, except broadcast lanes which snap to the
	// last leader's slot. This is SAT-proven equivalent to the unrolled RTL
	// allocation loop (taken[]/done[] scan).
	// ----------------------------------------------------------------
	struct AllocResult {
		vector<int> dsel;     // per-lane rank
		vector<char> leader;  // 1 iff lane is a slot leader
		vector<int> slot;     // exclusive prefix count of leaders
		int M = 0;            // number of leaders
	};

	AllocResult compute_alloc(const vector<int> &en, const vector<int> &bc,
	                          const vector<int> &cat, int n) const
	{
		AllocResult r;
		r.dsel.assign(n, 0);
		r.leader.assign(n, 0);
		r.slot.assign(n, 0);

		vector<char> any_en_before(n, 0);
		int acc = 0;
		for (int i = 0; i < n; i++) {
			any_en_before[i] = acc ? 1 : 0;
			acc |= en[i];
		}
		int e0 = -1;
		for (int i = 0; i < n; i++)
			if (en[i] && !any_en_before[i]) { e0 = i; break; }
		int cat_e0 = (e0 >= 0) ? cat[e0] : 0;

		for (int i = 0; i < n; i++) {
			bool is_e0 = (i == e0);
			bool blocked_mid = false;
			for (int j = 0; j < i; j++)
				if (any_en_before[j] && en[j] && !bc[j] && cat[j] == cat[i]) {
					blocked_mid = true;
					break;
				}
			bool eq_e0 = (cat[i] == cat_e0);
			r.leader[i] = en[i] && (is_e0 || (!bc[i] && !eq_e0 && !blocked_mid));
		}

		int cnt = 0;
		for (int i = 0; i < n; i++) {
			r.slot[i] = cnt;
			if (r.leader[i])
				cnt++;
		}
		r.M = cnt;

		for (int k = 0; k < n; k++) {
			if (bc[k]) {
				r.dsel[k] = (r.M >= 1) ? (r.M - 1) : 0;
			} else if (en[k]) {
				for (int i = 0; i < n; i++)
					if (r.leader[i] && cat[i] == cat[k]) {
						r.dsel[k] = r.slot[i];
						break;
					}
			}
		}
		return r;
	}

	// Direction-aware wrapper: reverse inputs for MSB-first scans.
	AllocResult compute_alloc_dir(const vector<int> &en, const vector<int> &bc,
	                              const vector<int> &cat, int n, bool msb_first) const
	{
		if (!msb_first)
			return compute_alloc(en, bc, cat, n);
		vector<int> er(n), br(n), cr(n);
		for (int i = 0; i < n; i++) {
			er[i] = en[n - 1 - i];
			br[i] = bc[n - 1 - i];
			cr[i] = cat[n - 1 - i];
		}
		AllocResult rr = compute_alloc(er, br, cr, n);
		AllocResult r;
		r.dsel.assign(n, 0);
		r.leader.assign(n, 0);
		r.slot.assign(n, 0);
		r.M = rr.M;
		for (int i = 0; i < n; i++) {
			r.dsel[i] = rr.dsel[n - 1 - i];
			r.leader[i] = rr.leader[n - 1 - i];
			r.slot[i] = rr.slot[n - 1 - i];
		}
		return r;
	}

	// ----------------------------------------------------------------
	// Reference semantics of the "coalesce matrix" allocator variant.
	//
	// Leadership and slot assignment are identical to the greedy first-fit
	// above, but the per-lane rank does NOT depend on the lane's own enable:
	// every lane k (enabled or not) inherits the slot of the first leader at
	// or before k (in priority order) whose category matches cat[k]. This
	// models RTL that precomputes a per-leader "same_cat[i][k]" mask (gated
	// only on the leader's enable) and forward-coalesces into lane k without
	// re-checking en[k]. There is no broadcast lane in this variant.
	// ----------------------------------------------------------------
	AllocResult compute_alloc_coalesce(const vector<int> &en, const vector<int> &cat,
	                                   int n) const
	{
		AllocResult r = compute_alloc(en, vector<int>(n, 0), cat, n);
		for (int k = 0; k < n; k++) {
			r.dsel[k] = 0;
			for (int i = 0; i <= k; i++)
				if (r.leader[i] && cat[i] == cat[k]) {
					r.dsel[k] = r.slot[i];
					break;
				}
		}
		return r;
	}

	AllocResult compute_alloc_coalesce_dir(const vector<int> &en, const vector<int> &cat,
	                                       int n, bool msb_first) const
	{
		if (!msb_first)
			return compute_alloc_coalesce(en, cat, n);
		vector<int> er(n), cr(n);
		for (int i = 0; i < n; i++) {
			er[i] = en[n - 1 - i];
			cr[i] = cat[n - 1 - i];
		}
		AllocResult rr = compute_alloc_coalesce(er, cr, n);
		AllocResult r;
		r.dsel.assign(n, 0);
		r.leader.assign(n, 0);
		r.slot.assign(n, 0);
		r.M = rr.M;
		for (int i = 0; i < n; i++) {
			r.dsel[i] = rr.dsel[n - 1 - i];
			r.leader[i] = rr.leader[n - 1 - i];
			r.slot[i] = rr.slot[n - 1 - i];
		}
		return r;
	}

	// ----------------------------------------------------------------
	// Reference semantics of the "exclusive saturating" first-fit variant
	// (no category, no broadcast). Enabled lanes are scanned in priority
	// order and each takes the next free slot until the slot budget nb is
	// exhausted; later requesters get no grant (rank 0, not done). This is
	// the qor_vmw_slot_lane shape.
	//
	//   rank[i] = popcount(en[<i])   (exclusive prefix count in prio order)
	//   grant[i] = en[i] && rank[i] < nb
	//   dsel[i]  = grant[i] ? rank[i] : 0
	// ----------------------------------------------------------------
	struct ExclResult {
		vector<int> dsel; // per-lane rank when granted, else 0
		vector<int> done; // per-lane grant
	};

	ExclResult compute_alloc_exclusive(const vector<int> &en, int n, int nb) const
	{
		ExclResult r;
		r.dsel.assign(n, 0);
		r.done.assign(n, 0);
		int acc = 0;
		for (int i = 0; i < n; i++) {
			int rank = acc; // exclusive: count of enables strictly before i
			bool grant = en[i] && rank < nb;
			r.done[i] = grant ? 1 : 0;
			r.dsel[i] = grant ? rank : 0;
			acc += en[i] ? 1 : 0;
		}
		return r;
	}

	// Direction-aware wrapper: reverse for MSB-first scans.
	ExclResult compute_alloc_exclusive_dir(const vector<int> &en, int n, int nb,
	                                       bool msb_first) const
	{
		if (!msb_first)
			return compute_alloc_exclusive(en, n, nb);
		vector<int> er(n);
		for (int i = 0; i < n; i++)
			er[i] = en[n - 1 - i];
		ExclResult rr = compute_alloc_exclusive(er, n, nb);
		ExclResult r;
		r.dsel.assign(n, 0);
		r.done.assign(n, 0);
		for (int i = 0; i < n; i++) {
			r.dsel[i] = rr.dsel[n - 1 - i];
			r.done[i] = rr.done[n - 1 - i];
		}
		return r;
	}

	// Enable-only test vectors for the exclusive variant: O(n) structured
	// cases (empty / full / singles / prefixes / suffixes) that straddle the
	// nb saturation boundary, plus a handful of pseudo-random masks.
	vector<vector<int>> make_exclusive_vectors(int n) const
	{
		vector<vector<int>> vs;
		vs.push_back(vector<int>(n, 0)); // all off
		vs.push_back(vector<int>(n, 1)); // all on (drives ranks past nb)
		for (int k = 0; k < n; k++) {    // single enabled lane
			vector<int> e(n, 0);
			e[k] = 1;
			vs.push_back(e);
		}
		for (int k = 0; k < n; k++) {    // prefix en[k..n-1]
			vector<int> e(n, 0);
			for (int j = k; j < n; j++)
				e[j] = 1;
			vs.push_back(e);
		}
		for (int k = 0; k < n; k++) {    // suffix en[0..k]
			vector<int> e(n, 0);
			for (int j = 0; j <= k; j++)
				e[j] = 1;
			vs.push_back(e);
		}
		uint64_t lfsr = 0xC0FFEE1234567ULL;
		for (int r = 0; r < 24; r++) {
			lfsr ^= lfsr << 13;
			lfsr ^= lfsr >> 7;
			lfsr ^= lfsr << 17;
			vector<int> e(n);
			for (int k = 0; k < n; k++)
				e[k] = (lfsr >> (k % 64)) & 1;
			vs.push_back(e);
		}
		return vs;
	}

	// Pack an enable pattern into the 2n-bit and2 enable signal: bit l and
	// bit n+l both hold en[l], so the reconstructed AND en[l]&en[n+l]==en[l].
	Const pack_exclusive_and2(const vector<int> &en, int n) const
	{
		vector<int> both(2 * n, 0);
		for (int l = 0; l < n; l++) {
			both[l] = en[l];
			both[n + l] = en[l];
		}
		return pack_lanes(both, 1);
	}

	// ----------------------------------------------------------------
	// Test vectors. `nval` is the number of distinct label values (2^c for
	// the category, 2^a for the xbar attribute). The vectors deliberately
	// include the all-distinct/all-enabled case so that an allocator whose
	// slot count is smaller than the number of distinct categories (i.e. one
	// that can overflow and diverge from the closed form) is rejected.
	// ----------------------------------------------------------------
	struct TestVector {
		vector<int> en;
		vector<int> bc;
		vector<int> label;
	};

	vector<TestVector> make_vectors(int n, int nval, bool with_bc) const
	{
		vector<TestVector> vs;
		auto lab = [&](int mul, int add) {
			vector<int> f(n);
			for (int k = 0; k < n; k++)
				f[k] = ((k * mul + add) % nval + nval) % nval;
			return f;
		};

		// All disabled.
		{ TestVector t; t.en.assign(n, 0); t.bc.assign(n, 0); t.label = lab(1, 0); vs.push_back(t); }

		// Single enabled lane (each lane), no bc.
		for (int k = 0; k < n; k++) {
			TestVector t; t.en.assign(n, 0); t.bc.assign(n, 0);
			t.en[k] = 1; t.label = lab(1, 0); vs.push_back(t);
		}

		// All enabled, all same category.
		{ TestVector t; t.en.assign(n, 1); t.bc.assign(n, 0); t.label.assign(n, 0); vs.push_back(t); }
		// All enabled, all distinct categories (overflow boundary).
		{ TestVector t; t.en.assign(n, 1); t.bc.assign(n, 0); t.label = lab(1, 0); vs.push_back(t); }
		{ TestVector t; t.en.assign(n, 1); t.bc.assign(n, 0); t.label = lab(3, 1); vs.push_back(t); }
		{ TestVector t; t.en.assign(n, 1); t.bc.assign(n, 0); t.label = lab(-1, nval - 1); vs.push_back(t); }

		// Prefix enable masks en[k..n-1].
		for (int k = 0; k < n; k++) {
			TestVector t; t.en.assign(n, 0); t.bc.assign(n, 0);
			for (int j = k; j < n; j++) t.en[j] = 1;
			t.label = lab(5, 2); vs.push_back(t);
		}
		// Suffix enable masks en[0..k].
		for (int k = 0; k < n; k++) {
			TestVector t; t.en.assign(n, 0); t.bc.assign(n, 0);
			for (int j = 0; j <= k; j++) t.en[j] = 1;
			t.label = lab(7, 3); vs.push_back(t);
		}

		// Pairs with distinct categories.
		for (int i = 0; i < n; i++)
			for (int j = i + 1; j < n && j < i + 3; j++) {
				TestVector t; t.en.assign(n, 0); t.bc.assign(n, 0);
				t.en[i] = 1; t.en[j] = 1; t.label = lab(2, 0);
				t.label[i] = (i + 1) % nval; t.label[j] = (j + 5) % nval;
				vs.push_back(t);
			}

		// Broadcast corners.
		if (with_bc) {
			// One bc lane among several enabled lanes.
			for (int b = 0; b < n; b += std::max(1, n / 6)) {
				TestVector t; t.en.assign(n, 1); t.bc.assign(n, 0);
				t.bc[b] = 1; t.label = lab(3, 0); vs.push_back(t);
			}
			// Leading bc lane (bc lane is E0).
			{ TestVector t; t.en.assign(n, 1); t.bc.assign(n, 0); t.bc[0] = 1; t.label = lab(1, 0); vs.push_back(t); }
			// bc lane not enabled.
			{ TestVector t; t.en.assign(n, 0); t.bc.assign(n, 0);
			  for (int j = 0; j < n; j += 2) t.en[j] = 1;
			  t.bc[1] = 1; t.bc[3 % n] = 1; t.label = lab(2, 1); vs.push_back(t); }
			// All bc, all enabled.
			{ TestVector t; t.en.assign(n, 1); t.bc.assign(n, 1); t.label = lab(1, 0); vs.push_back(t); }
		}

		// Pseudo-random coverage.
		uint64_t lfsr = 0x1234567089abcdefULL;
		for (int r = 0; r < 40; r++) {
			lfsr ^= lfsr << 13;
			lfsr ^= lfsr >> 7;
			lfsr ^= lfsr << 17;
			TestVector t; t.en.resize(n); t.bc.resize(n); t.label.resize(n);
			uint64_t f = lfsr * 2654435761ULL;
			// bc draws from an independently mixed word so en[k] and bc[j] never
			// share an LFSR bit (a shifted view of `lfsr` would alias them, e.g.
			// en[7] and bc[0] for n=8), keeping the random coverage independent.
			uint64_t g = lfsr * 0x9E3779B97F4A7C15ULL;
			for (int k = 0; k < n; k++) {
				t.en[k] = (lfsr >> (k % 64)) & 1;
				t.bc[k] = with_bc ? ((g >> (k % 64)) & 1) : 0;
				t.label[k] = (int)((f >> ((k * 3) % 60)) % (uint64_t)nval);
			}
			vs.push_back(t);
		}
		return vs;
	}

	// ----------------------------------------------------------------
	// Evaluate `out_sig` under input assignments, returning the full Const.
	// ----------------------------------------------------------------
	bool eval_root(ConstEval &ce, const vector<std::pair<SigSpec, Const>> &sets,
	               const SigSpec &out_sig, Const &result, int64_t cone_est)
	{
		charge_eval(cone_est);
		ce.push();
		for (auto &s : sets)
			ce.set(s.first, s.second);
		SigSpec out = out_sig;
		SigSpec undef;
		bool ok = ce.eval(out, undef);
		if (ok && out.is_fully_const())
			result = out.as_const();
		else
			ok = false;
		ce.pop();
		return ok;
	}

	static int lane_val(const Const &c, int lane, int elem_w)
	{
		int v = 0;
		for (int b = 0; b < elem_w; b++) {
			int p = lane * elem_w + b;
			if (p < GetSize(c) && c[p] == State::S1)
				v |= 1 << b;
		}
		return v;
	}

	// ----------------------------------------------------------------
	// Group a set of cone-leaf bits into per-lane fields of equal width,
	// using each bit's wire/offset and the wire's lane stride (width / n).
	// Returns a lane-major SigSpec (lane k -> bits [k*c +: c]) and the per-
	// lane width c, plus, for each cat key, the (wire,offset) identity so a
	// caller can locate the cat sub-field inside a wider attr field.
	// ----------------------------------------------------------------
	// A per-lane sub-field is identified by (source id, within-lane offset),
	// where the source is either a flat lane-strided bus (id = wire name) or
	// a group of per-lane indexed wires "base[i]" (id = base name). This lets
	// a category span several differently-laid-out buses (e.g. a flat set_q[]
	// plus per-lane bank_q[i][1:0] wires).
	struct FieldKey {
		std::string id;
		int offset;
		bool operator<(const FieldKey &o) const {
			if (id != o.id)
				return id < o.id;
			return offset < o.offset;
		}
		bool operator==(const FieldKey &o) const {
			return id == o.id && offset == o.offset;
		}
	};

	// Resolve a single cone-leaf bit to the lane it belongs to. Returns the
	// source `id` (flat bus wire name, or base name for per-lane "base[i]"
	// wires), the `lane` index in [0,n), and the bit's `offset` within that
	// lane's sub-field. Returns false if the bit has no wire or cannot be
	// assigned to one of the n lanes.
	bool lane_of_bit(SigBit bit, int n, std::string &id, int &lane, int &offset)
	{
		if (!bit.wire)
			return false;
		Wire *w = bit.wire;
		std::string base;
		int idx = -1;
		if (parse_indexed_port_name(w, base, idx)) {
			id = base;
			lane = idx;
			offset = bit.offset;
		} else {
			int width = GetSize(w);
			if (width % n != 0)
				return false;
			int stride = width / n;
			id = w->name.str();
			lane = bit.offset / stride;
			offset = bit.offset % stride;
		}
		return lane >= 0 && lane < n;
	}

	bool group_lane_field(const pool<SigBit> &bits, int n, SigSpec &field,
	                      int &c, vector<FieldKey> *keys_out = nullptr)
	{
		if (bits.empty() || n <= 0)
			return false;
		// Per-lane indexed wires may start at a non-zero base index; normalize
		// each source's lane numbering to start at its minimum.
		dict<std::string, int> src_min_lane;
		vector<std::tuple<std::string, int, int, SigBit>> recs; // id, lane, off, bit
		for (auto bit : bits) {
			std::string id;
			int lane, off;
			if (!lane_of_bit(bit, n, id, lane, off))
				return false;
			if (!src_min_lane.count(id) || lane < src_min_lane[id])
				src_min_lane[id] = lane;
			recs.push_back({id, lane, off, bit});
		}
		vector<std::map<FieldKey, SigBit>> per_lane(n);
		for (auto &r : recs) {
			std::string id = std::get<0>(r);
			int lane = std::get<1>(r) - src_min_lane[id];
			int off = std::get<2>(r);
			if (lane < 0 || lane >= n)
				return false;
			if (!per_lane[lane].emplace(FieldKey{id, off}, std::get<3>(r)).second)
				return false;
		}
		std::set<FieldKey> keys;
		for (auto &kv : per_lane[0])
			keys.insert(kv.first);
		if (keys.empty())
			return false;
		for (int k = 0; k < n; k++) {
			if (GetSize(per_lane[k]) != GetSize(keys))
				return false;
			for (auto &kv : per_lane[k])
				if (!keys.count(kv.first))
					return false;
		}
		c = GetSize(keys);
		field = SigSpec();
		vector<FieldKey> ordered(keys.begin(), keys.end());
		for (int k = 0; k < n; k++)
			for (auto &key : ordered)
				field.append(per_lane[k].at(key));
		if (keys_out != nullptr)
			*keys_out = ordered;
		return true;
	}

	// ----------------------------------------------------------------
	// A matched region: the shared (en,bc,cat) scan plus the dsel root.
	// ----------------------------------------------------------------
	struct Region {
		// dsel
		SigSpec dsel_sig;
		std::string dsel_name;
		int n = 0;
		int field_w = 0;
		SigSpec en_sig, bc_sig, cat_sig;
		bool has_bc = false;
		// Enable-independent forward coalescing: lanes inherit the slot of the
		// first same-category leader at or before them in priority order,
		// regardless of their own enable (the "same_cat matrix" RTL shape).
		bool coalesce = false;
		// Exclusive saturating first-fit (no category / broadcast): each
		// enabled lane takes the next free slot until nb slots are used.
		bool exclusive = false;
		// The enable was reconstructed as the AND of two leaf runs (en_sig is
		// the 2n-bit concatenation runA ++ runB; en[l] = runA[l] & runB[l]).
		bool exclusive_and2 = false;
		int nb = 0; // learned slot budget for the exclusive variant
		int c = 0;
		bool msb_first = false;
		Cell *anchor = nullptr;
		pool<Cell *> dsel_cut_cells;
		vector<FieldKey> cat_keys;
	};

	// ---- small emit helpers ----
	SigBit emit_not(Cell *anchor, SigBit a)
	{
		Cell *cell = anchor;
		SigBit o = module->Not(NEW_ID2_SUFFIX("ffa_not"), SigSpec(a), false, cell_src(anchor))[0];
		cells_added++;
		return o;
	}
	SigBit emit_and(Cell *anchor, SigBit a, SigBit b)
	{
		// Const-fold 0/1 operands so prefix-OR / category scans don't emit
		// dead $and cells that only inflate cells_added until opt_expr.
		if (a == State::S0 || b == State::S0)
			return State::S0;
		if (a == State::S1)
			return b;
		if (b == State::S1)
			return a;
		Cell *cell = anchor;
		SigBit o = module->And(NEW_ID2_SUFFIX("ffa_and"), SigSpec(a), SigSpec(b), false, cell_src(anchor))[0];
		cells_added++;
		return o;
	}
	SigBit emit_or(Cell *anchor, SigBit a, SigBit b)
	{
		// Same for $or: exclusive prefix starts at S0 and would otherwise
		// produce a cascade of (x | 0) cells on every Hillis-Steele step.
		if (a == State::S1 || b == State::S1)
			return State::S1;
		if (a == State::S0)
			return b;
		if (b == State::S0)
			return a;
		Cell *cell = anchor;
		SigBit o = module->Or(NEW_ID2_SUFFIX("ffa_or"), SigSpec(a), SigSpec(b), false, cell_src(anchor))[0];
		cells_added++;
		return o;
	}
	SigBit emit_reduce_or(Cell *anchor, SigSpec bits)
	{
		bits = sigmap(bits);
		if (GetSize(bits) == 0)
			return State::S0;
		if (GetSize(bits) == 1)
			return bits[0];
		Cell *cell = anchor;
		SigBit o = module->ReduceOr(NEW_ID2_SUFFIX("ffa_ror"), bits, false, cell_src(anchor))[0];
		cells_added++;
		return o;
	}

	// Hillis-Steele exclusive prefix-OR: out[0]=0, out[i]=OR(bits[0..i-1]).
	// Shared log-depth network instead of a fresh ReduceOr per position.
	void emit_prefix_or_excl(Cell *anchor, const vector<SigBit> &bits,
	                         vector<SigBit> &out)
	{
		int n = GetSize(bits);
		out.assign(n, State::S0);
		if (n == 0)
			return;
		vector<SigBit> cur = bits;
		for (int d = 1; d < n; d <<= 1) {
			vector<SigBit> nxt = cur;
			for (int i = d; i < n; i++)
				nxt[i] = emit_or(anchor, cur[i], cur[i - d]);
			cur.swap(nxt);
		}
		out[0] = State::S0;
		for (int i = 1; i < n; i++)
			out[i] = cur[i - 1];
	}
	SigBit emit_eq_sig(Cell *anchor, SigSpec a, SigSpec b)
	{
		Cell *cell = anchor;
		SigBit o = module->Eq(NEW_ID2_SUFFIX("ffa_eq"), a, b, false, cell_src(anchor))[0];
		cells_added++;
		return o;
	}
	SigBit emit_eq_const(Cell *anchor, SigSpec a, int value, int width)
	{
		return emit_eq_sig(anchor, zext_sig(a, width), Const(value, width));
	}
	SigSpec emit_mux(Cell *anchor, SigSpec a, SigSpec b, SigBit s)
	{
		Cell *cell = anchor;
		SigSpec o = module->Mux(NEW_ID2_SUFFIX("ffa_mux"), a, b, SigSpec(s), cell_src(anchor));
		cells_added++;
		return o;
	}
	SigSpec emit_bmux(Cell *anchor, SigSpec table, SigSpec sel, int width)
	{
		Cell *cell = anchor;
		Wire *o = module->addWire(NEW_ID2_SUFFIX("ffa_bmux"), width);
		module->addBmux(NEW_ID2_SUFFIX("ffa_bmux_cell"), table, sel, o, cell_src(anchor));
		cells_added++;
		return SigSpec(o);
	}

	// Exclusive prefix-sum of `bits` as a linear $add cascade. Each running
	// sum is consumed downstream, so opt_parallel_prefix -arith later rebuilds
	// the cascade into a shared log-depth network. Returns slot[i] and the
	// total M (inclusive sum).
	void emit_prefix_count(Cell *anchor, const vector<SigBit> &bits, int cnt_w,
	                       vector<SigSpec> &slot, SigSpec &total)
	{
		Cell *cell = anchor;
		int n = GetSize(bits);
		slot.assign(n, SigSpec());
		SigSpec acc = Const(0, cnt_w);
		for (int i = 0; i < n; i++) {
			slot[i] = acc;
			Wire *sum = module->addWire(NEW_ID2_SUFFIX("ffa_pre"), cnt_w);
			module->addAdd(NEW_ID2_SUFFIX("ffa_pre_add"), acc, SigSpec(bits[i]), sum, false, cell_src(anchor));
			cells_added++;
			acc = SigSpec(sum);
		}
		total = acc;
	}

	// ---- exclusive-variant emit helpers ----

	// slot < nb, as a 1-bit $lt against a constant (cnt_w-wide compare).
	SigBit emit_lt_const(Cell *anchor, SigSpec a, int value, int width)
	{
		Cell *cell = anchor;
		a = zext_sig(a, width);
		Wire *o = module->addWire(NEW_ID2_SUFFIX("ffa_excl_lt"), 1);
		module->addLt(NEW_ID2_SUFFIX("ffa_excl_lt_cell"), a, Const(value, width), o, false, cell_src(anchor));
		cells_added++;
		return SigBit(o, 0);
	}

	// grant[l] = en[l] && (slot[l] < nb): the saturating first-fit gate. The
	// prefix count feeding slot is a plain $add cascade (no per-step mux), so
	// opt_parallel_prefix -arith rebuilds it into a shared log-depth network.
	SigBit emit_grant(Cell *anchor, SigBit en, SigSpec slot, int cnt_w, int nb)
	{
		SigBit lt = emit_lt_const(anchor, slot, nb, cnt_w);
		return emit_and(anchor, en, lt);
	}

	// Saturating add: min(a + b, sat). Widen the add by 1 so two already-
	// saturated operands cannot wrap (e.g. nb=4, cnt_w=3: 4+4 must stay 4,
	// not 0). Fallback exclusive scan when nb is too large for a thermometer.
	SigSpec emit_sat_add(Cell *anchor, SigSpec a, SigSpec b, int sat, int cnt_w)
	{
		Cell *cell = anchor;
		int aw = cnt_w + 1;
		a = zext_sig(a, aw);
		b = zext_sig(b, aw);
		Wire *sum = module->addWire(NEW_ID2_SUFFIX("ffa_sat_add"), aw);
		module->addAdd(NEW_ID2_SUFFIX("ffa_sat_add_cell"), a, b, sum, false, cell_src(anchor));
		cells_added++;
		Wire *ltw = module->addWire(NEW_ID2_SUFFIX("ffa_sat_lt"), 1);
		module->addLt(NEW_ID2_SUFFIX("ffa_sat_lt_cell"), SigSpec(sum), Const(sat, aw), ltw,
		              /*is_signed=*/false, cell_src(anchor));
		cells_added++;
		SigSpec capped = emit_mux(anchor, Const(sat, aw), SigSpec(sum), SigBit(ltw));
		return capped.extract(0, cnt_w);
	}

	// Hillis-Steele inclusive scan with saturating add; exclusive slot[i] =
	// inclusive[i-1]. Used when nb > max_therm_nb.
	void emit_prefix_count_sat_log(Cell *anchor, const vector<SigBit> &bits, int cnt_w,
	                               int sat, vector<SigSpec> &slot, SigSpec &total)
	{
		int n = GetSize(bits);
		slot.assign(n, SigSpec());
		if (n == 0) {
			total = Const(0, cnt_w);
			return;
		}
		vector<SigSpec> cur(n);
		for (int i = 0; i < n; i++)
			cur[i] = zext_sig(SigSpec(bits[i]), cnt_w);

		for (int d = 1; d < n; d <<= 1) {
			vector<SigSpec> nxt = cur;
			for (int i = d; i < n; i++)
				nxt[i] = emit_sat_add(anchor, cur[i], cur[i - d], sat, cnt_w);
			cur.swap(nxt);
		}
		total = cur[n - 1];
		slot[0] = Const(0, cnt_w);
		for (int i = 1; i < n; i++)
			slot[i] = cur[i - 1];
	}

	// Thermometer bit k means count > k (i.e. count >= k+1), width nb.
	// Merge: (a+b) > k iff exists i: a>=i && b>=(k+1-i).
	SigSpec emit_therm_merge(Cell *anchor, SigSpec ta, SigSpec tb, int nb)
	{
		log_assert(GetSize(ta) == nb && GetSize(tb) == nb);
		SigSpec out;
		for (int k = 0; k < nb; k++) {
			SigSpec terms;
			for (int i = 0; i <= k + 1; i++) {
				SigBit a_ge = (i == 0) ? State::S1 : ta[i - 1];
				int bj = k + 1 - i;
				SigBit b_ge = (bj == 0) ? State::S1 : tb[bj - 1];
				terms.append(emit_and(anchor, a_ge, b_ge));
			}
			out.append(emit_reduce_or(anchor, terms));
		}
		return out;
	}

	// One-bit enable -> nb-bit thermometer (count 0 or 1).
	SigSpec emit_therm_from_bit(SigBit b, int nb)
	{
		SigSpec t;
		t.append(b);
		for (int k = 1; k < nb; k++)
			t.append(State::S0);
		return t;
	}

	// Binary popcount of thermometer bits (= the saturated count). Tree-shaped
	// so depth is O(log nb) rather than a serial ripple of nb adds.
	SigSpec emit_therm_to_bin(Cell *anchor, SigSpec therm, int cnt_w)
	{
		Cell *cell = anchor;
		vector<SigSpec> nodes;
		for (auto bit : therm)
			nodes.push_back(zext_sig(SigSpec(bit), cnt_w));
		if (nodes.empty())
			return Const(0, cnt_w);
		while (GetSize(nodes) > 1) {
			vector<SigSpec> nxt;
			for (int i = 0; i + 1 < GetSize(nodes); i += 2) {
				Wire *sum = module->addWire(NEW_ID2_SUFFIX("ffa_therm_bin"), cnt_w);
				module->addAdd(NEW_ID2_SUFFIX("ffa_therm_bin_add"), nodes[i], nodes[i + 1], sum, false, cell_src(anchor));
				cells_added++;
				nxt.push_back(SigSpec(sum));
			}
			if (GetSize(nodes) & 1)
				nxt.push_back(nodes.back());
			nodes.swap(nxt);
		}
		return nodes[0];
	}

	// count == s from thermometer (s in 0..nb-1): therm[s-1] & ~therm[s].
	SigBit emit_therm_eq(Cell *anchor, SigSpec therm, int s, int nb)
	{
		log_assert(s >= 0 && s < nb && GetSize(therm) == nb);
		if (s == 0)
			return emit_not(anchor, therm[0]);
		return emit_and(anchor, therm[s - 1], emit_not(anchor, therm[s]));
	}

	// Log-depth exclusive thermometer prefix (saturated at nb).
	void emit_prefix_therm_log(Cell *anchor, const vector<SigBit> &bits, int nb,
	                           vector<SigSpec> &therm_excl)
	{
		int n = GetSize(bits);
		therm_excl.assign(n, SigSpec());
		if (n == 0)
			return;
		vector<SigSpec> cur(n);
		for (int i = 0; i < n; i++)
			cur[i] = emit_therm_from_bit(bits[i], nb);

		for (int d = 1; d < n; d <<= 1) {
			vector<SigSpec> nxt = cur;
			for (int i = d; i < n; i++)
				nxt[i] = emit_therm_merge(anchor, cur[i], cur[i - d], nb);
			cur.swap(nxt);
		}
		therm_excl[0] = Const(0, nb);
		for (int i = 1; i < n; i++)
			therm_excl[i] = cur[i - 1];
	}

	// Build priority-ordered enables for the exclusive scan.
	void exclusive_en_prio(const Region &rg, vector<SigBit> &en_p, vector<int> &lane_of_p)
	{
		Cell *anchor = rg.anchor;
		int n = rg.n;
		SigSpec en = sigmap(rg.en_sig);
		en_p.resize(n);
		lane_of_p.resize(n);
		for (int p = 0; p < n; p++) {
			int l = rg.msb_first ? (n - 1 - p) : p;
			lane_of_p[p] = l;
			if (rg.exclusive_and2) {
				log_assert(GetSize(en) == 2 * n);
				en_p[p] = emit_and(anchor, en[l], en[n + l]);
			} else {
				en_p[p] = en[l];
			}
		}
	}

	// Exclusive scan via nb-bit thermometer (preferred for small nb).
	void emit_scan_exclusive_therm(const Region &rg, vector<SigBit> &leader,
	                               vector<SigSpec> &therm, vector<SigBit> &grant,
	                               vector<SigSpec> &slot, int cnt_w)
	{
		Cell *anchor = rg.anchor;
		int n = rg.n, nb = rg.nb;
		vector<SigBit> en_p;
		vector<int> lane_of_p;
		exclusive_en_prio(rg, en_p, lane_of_p);

		vector<SigSpec> therm_p;
		emit_prefix_therm_log(anchor, en_p, nb, therm_p);

		leader.assign(n, SigBit());
		therm.assign(n, SigSpec());
		grant.assign(n, SigBit());
		slot.assign(n, SigSpec());
		for (int p = 0; p < n; p++) {
			int l = lane_of_p[p];
			leader[l] = en_p[p];
			therm[l] = therm_p[p];
			// grant = en && (count < nb) = en && ~(count > nb-1)
			grant[l] = emit_and(anchor, en_p[p], emit_not(anchor, therm_p[p][nb - 1]));
			slot[l] = emit_therm_to_bin(anchor, therm_p[p], cnt_w);
		}
	}

	// Exclusive scan via narrow saturating binary prefix (large-nb fallback).
	void emit_scan_exclusive_bin(const Region &rg, vector<SigBit> &leader,
	                             vector<SigSpec> &slot, vector<SigBit> &grant, int cnt_w)
	{
		Cell *anchor = rg.anchor;
		int n = rg.n;
		vector<SigBit> en_p;
		vector<int> lane_of_p;
		exclusive_en_prio(rg, en_p, lane_of_p);

		vector<SigSpec> slot_p;
		SigSpec total;
		emit_prefix_count_sat_log(anchor, en_p, cnt_w, rg.nb, slot_p, total);

		leader.assign(n, SigBit());
		slot.assign(n, SigSpec());
		grant.assign(n, SigBit());
		for (int p = 0; p < n; p++) {
			int l = lane_of_p[p];
			leader[l] = en_p[p];
			slot[l] = slot_p[p];
			grant[l] = emit_grant(anchor, en_p[p], slot_p[p], cnt_w, rg.nb);
		}
	}

	// dsel gather for the exclusive variant: dsel[l] = grant[l] ? slot[l] : 0.
	SigSpec emit_dsel_exclusive(const Region &rg, const vector<SigBit> &grant,
	                            const vector<SigSpec> &slot, int cnt_w)
	{
		Cell *anchor = rg.anchor;
		int n = rg.n, w = rg.field_w;
		SigSpec out;
		for (int l = 0; l < n; l++) {
			SigSpec val = emit_mux(anchor, Const(0, cnt_w), slot[l], grant[l]);
			out.append(zext_sig(val, w));
		}
		return out;
	}

	// done[l] = grant[l] (the same saturating first-fit gate).
	SigSpec emit_exclusive_done(const Region &rg, const vector<SigBit> &grant)
	{
		SigSpec out;
		for (int l = 0; l < rg.n; l++)
			out.append(grant[l]);
		return out;
	}

	// Emit the shared leader/slot scan from (en,bc,cat). Fills leader[],
	// slot[] (cnt_w bits), total M, and the lane categories cat_lane[].
	// Optionally fills therm[] (nb-bit exclusive thermometer of leaders) when
	// use_therm is true so xbar/dsel can avoid binary slot==s compares.
	void emit_scan(const Region &rg, vector<SigBit> &leader, vector<SigSpec> &slot,
	               SigSpec &total, int cnt_w, vector<SigSpec> &cat_lane,
	               vector<SigSpec> *therm = nullptr, int therm_nb = 0)
	{
		Cell *anchor = rg.anchor;
		int n = rg.n, c = rg.c;
		SigSpec en = sigmap(rg.en_sig);
		SigSpec bc = rg.has_bc ? sigmap(rg.bc_sig) : SigSpec();
		SigSpec cat = sigmap(rg.cat_sig);

		// priority order: index p -> lane
		auto lane_of = [&](int p) { return rg.msb_first ? (n - 1 - p) : p; };

		vector<SigBit> en_p(n), bc_p(n);
		cat_lane.assign(n, SigSpec());
		for (int p = 0; p < n; p++) {
			int l = lane_of(p);
			en_p[p] = en[l];
			bc_p[p] = rg.has_bc ? bc[l] : SigBit(State::S0);
			cat_lane[p] = cat.extract(l * c, c);
		}

		// anyEnBefore[p] = OR_{q<p} en_p[q] via shared log-depth prefix-OR
		vector<SigBit> any_before;
		emit_prefix_or_excl(anchor, en_p, any_before);

		// isE0[p] = en_p[p] & ~anyEnBefore[p]
		vector<SigBit> is_e0(n);
		for (int p = 0; p < n; p++)
			is_e0[p] = emit_and(anchor, en_p[p], emit_not(anchor, any_before[p]));
		// catE0[b] = OR_p (isE0[p] & cat[p][b])
		SigSpec cat_e0;
		for (int b = 0; b < c; b++) {
			SigSpec terms;
			for (int p = 0; p < n; p++)
				terms.append(emit_and(anchor, is_e0[p], cat_lane[p][b]));
			cat_e0.append(emit_reduce_or(anchor, terms));
		}
		// eqE0[p] = (cat[p]==catE0)
		vector<SigBit> eq_e0(n);
		for (int p = 0; p < n; p++)
			eq_e0[p] = emit_eq_sig(anchor, cat_lane[p], cat_e0);

		// Category-indexed leadership: for each small key v, exclusive
		// prefix-OR of (qual & cat==v) replaces the O(n^2) pairwise blockedMid.
		// qual[p] = anyEnBefore[p] & en_p[p] & ~bc_p[p]
		vector<SigBit> qual(n);
		for (int p = 0; p < n; p++) {
			SigBit t = emit_and(anchor, any_before[p], en_p[p]);
			qual[p] = emit_and(anchor, t, emit_not(anchor, bc_p[p]));
		}

		log_assert(c >= 0 && c <= max_cat_w);
		int ncat = 1 << c;
		vector<vector<SigBit>> blocked_by_cat(ncat);
		for (int v = 0; v < ncat; v++) {
			vector<SigBit> bits(n);
			for (int p = 0; p < n; p++) {
				SigBit is_v = emit_eq_const(anchor, cat_lane[p], v, c);
				bits[p] = emit_and(anchor, qual[p], is_v);
			}
			emit_prefix_or_excl(anchor, bits, blocked_by_cat[v]);
		}
		// blockedMid[p] = any same-cat qual before p (mux of per-cat prefix-ORs)
		vector<SigBit> blocked_mid(n);
		for (int p = 0; p < n; p++) {
			SigBit b = State::S0;
			for (int v = 0; v < ncat; v++) {
				SigBit is_v = emit_eq_const(anchor, cat_lane[p], v, c);
				b = emit_or(anchor, b, emit_and(anchor, is_v, blocked_by_cat[v][p]));
			}
			blocked_mid[p] = b;
		}

		// leader[p] = en_p[p] & (isE0[p] | (~bc_p[p] & ~eqE0[p] & ~blockedMid[p]))
		vector<SigBit> leader_p(n);
		for (int p = 0; p < n; p++) {
			SigBit a = emit_and(anchor, emit_not(anchor, bc_p[p]), emit_not(anchor, eq_e0[p]));
			a = emit_and(anchor, a, emit_not(anchor, blocked_mid[p]));
			SigBit b = emit_or(anchor, is_e0[p], a);
			leader_p[p] = emit_and(anchor, en_p[p], b);
		}

		// slot[p] = exclusive prefix count; prefer thermometer when nb is small
		vector<SigSpec> slot_p;
		vector<SigSpec> therm_p;
		bool use_therm = therm && therm_nb >= 1 && therm_nb <= max_therm_nb;
		if (use_therm) {
			emit_prefix_therm_log(anchor, leader_p, therm_nb, therm_p);
			slot_p.resize(n);
			for (int p = 0; p < n; p++)
				slot_p[p] = emit_therm_to_bin(anchor, therm_p[p], cnt_w);
			// total M = inclusive count = merge(excl[n-1], leader[n-1])
			if (n == 0) {
				total = Const(0, cnt_w);
			} else {
				SigSpec last = emit_therm_merge(anchor, therm_p[n - 1],
				                                emit_therm_from_bit(leader_p[n - 1], therm_nb),
				                                therm_nb);
				total = emit_therm_to_bin(anchor, last, cnt_w);
			}
		} else {
			emit_prefix_count(anchor, leader_p, cnt_w, slot_p, total);
		}

		// map priority order back to lanes
		leader.assign(n, SigBit());
		slot.assign(n, SigSpec());
		if (therm)
			therm->assign(n, SigSpec());
		for (int p = 0; p < n; p++) {
			int l = lane_of(p);
			leader[l] = leader_p[p];
			slot[l] = slot_p[p];
			if (use_therm)
				(*therm)[l] = therm_p[p];
		}
	}

	// dsel gather. Returns lane-major SigSpec (lane k -> [k*field_w +: field_w]).
	SigSpec emit_dsel(const Region &rg, const vector<SigBit> &leader,
	                  const vector<SigSpec> &slot, SigSpec total, int cnt_w)
	{
		Cell *anchor = rg.anchor;
		int n = rg.n, c = rg.c, w = rg.field_w;
		SigSpec cat = sigmap(rg.cat_sig);
		log_assert(c >= 0 && c <= max_cat_w);
		int ncat = 1 << c;

		// Per-category slot of the unique leader with that cat (OR-of-AND).
		// Shared across all lanes so we avoid an O(n^2) cat-equality matrix.
		vector<SigSpec> slot_of_cat(ncat, Const(0, cnt_w));
		vector<SigBit> cat_is(n * ncat);
		for (int i = 0; i < n; i++) {
			SigSpec cat_i = cat.extract(i * c, c);
			for (int v = 0; v < ncat; v++)
				cat_is[i * ncat + v] = emit_eq_const(anchor, cat_i, v, c);
		}
		for (int v = 0; v < ncat; v++) {
			SigSpec rank(Const(0, cnt_w));
			for (int b = 0; b < cnt_w; b++) {
				SigSpec terms;
				for (int i = 0; i < n; i++)
					terms.append(emit_and(anchor, emit_and(anchor, leader[i], cat_is[i * ncat + v]),
					                      slot[i][b]));
				rank[b] = emit_reduce_or(anchor, terms);
			}
			slot_of_cat[v] = rank;
		}
		auto mux_slot_by_cat = [&](SigSpec cat_k) -> SigSpec {
			SigSpec rank(Const(0, cnt_w));
			for (int b = 0; b < cnt_w; b++) {
				SigSpec terms;
				for (int v = 0; v < ncat; v++) {
					SigBit is_v = emit_eq_const(anchor, cat_k, v, c);
					terms.append(emit_and(anchor, is_v, slot_of_cat[v][b]));
				}
				rank[b] = emit_reduce_or(anchor, terms);
			}
			return rank;
		};

		// Enable-independent forward coalescing: lane k inherits the slot of the
		// unique same-category leader at or before k in priority order.
		if (rg.coalesce) {
			auto pos = [&](int l) { return rg.msb_first ? (n - 1 - l) : l; };
			vector<SigBit> leader_p(n);
			vector<SigSpec> slot_p(n);
			vector<int> lane_of_p(n);
			for (int p = 0; p < n; p++) {
				int l = rg.msb_first ? (n - 1 - p) : p;
				lane_of_p[p] = l;
				leader_p[p] = leader[l];
				slot_p[p] = slot[l];
			}
			// Per category: inclusive OR-scan of (leader & cat==v) * slot bits.
			// After the scan, slot_at[v][p] is the slot of the latest same-cat
			// leader at or before priority position p (0 if none).
			vector<vector<SigSpec>> slot_at(ncat);
			for (int v = 0; v < ncat; v++) {
				vector<SigSpec> cur(n);
				for (int p = 0; p < n; p++) {
					SigBit g = emit_and(anchor, leader_p[p], cat_is[lane_of_p[p] * ncat + v]);
					SigSpec val(Const(0, cnt_w));
					for (int b = 0; b < cnt_w; b++)
						val[b] = emit_and(anchor, g, slot_p[p][b]);
					cur[p] = val;
				}
				// Hillis-Steele inclusive OR-scan over cnt_w-bit vectors
				for (int d = 1; d < n; d <<= 1) {
					vector<SigSpec> nxt = cur;
					for (int p = d; p < n; p++) {
						SigSpec m(Const(0, cnt_w));
						for (int b = 0; b < cnt_w; b++)
							m[b] = emit_or(anchor, cur[p][b], cur[p - d][b]);
						nxt[p] = m;
					}
					cur.swap(nxt);
				}
				slot_at[v] = cur;
			}
			SigSpec out;
			for (int k = 0; k < n; k++) {
				int p = pos(k);
				SigSpec cat_k = cat.extract(k * c, c);
				SigSpec rank(Const(0, cnt_w));
				for (int b = 0; b < cnt_w; b++) {
					SigSpec terms;
					for (int v = 0; v < ncat; v++) {
						SigBit is_v = emit_eq_const(anchor, cat_k, v, c);
						terms.append(emit_and(anchor, is_v, slot_at[v][p][b]));
					}
					rank[b] = emit_reduce_or(anchor, terms);
				}
				out.append(zext_sig(rank, w));
			}
			return out;
		}

		SigSpec en = sigmap(rg.en_sig);
		SigSpec bc = rg.has_bc ? sigmap(rg.bc_sig) : SigSpec();

		// bc rank: (M>=1) ? M-1 : 0
		SigBit any_leader = emit_reduce_or(anchor, total);
		Cell *cell = anchor;
		Wire *mm1w = module->addWire(NEW_ID2_SUFFIX("ffa_Mm1"), cnt_w);
		module->addSub(NEW_ID2_SUFFIX("ffa_Mm1_sub"), total, Const(1, cnt_w), mm1w, false, cell_src(anchor));
		cells_added++;
		SigSpec bc_rank = emit_mux(anchor, Const(0, cnt_w), SigSpec(mm1w), any_leader);

		SigSpec out;
		for (int k = 0; k < n; k++) {
			SigSpec cat_k = cat.extract(k * c, c);
			SigSpec en_rank = mux_slot_by_cat(cat_k);
			// dsel[k] = bc[k] ? bc_rank : (en[k] ? en_rank : 0)
			SigSpec sel_en = emit_mux(anchor, Const(0, cnt_w), en_rank, en[k]);
			SigSpec val = sel_en;
			if (rg.has_bc)
				val = emit_mux(anchor, sel_en, bc_rank, bc[k]);
			out.append(zext_sig(val, w));
		}
		return out;
	}

	// ----------------------------------------------------------------
	// xbar (per-slot field gather): xbar_slot[s] = (s<M) ? f(attr[leader at
	// slot s]) : 0, where f is learned by ConstEval (single-leader probe).
	// Emit applies f per-lane first (parallel with the scan), then one-hot
	// gathers the result — keeps the table mux off the post-scan critical path.
	// ----------------------------------------------------------------
	struct XbarCand {
		SigSpec sig;
		std::string name;
		int nb = 0;       // number of slots
		int slot_w = 0;   // bits per slot block
		SigSpec attr_sig; // lane-major attr
		int a = 0;        // attr width per lane
		vector<Const> ftab; // 2^a entries, slot_w bits each
		vector<FieldKey> attr_keys;
		bool identity = false; // exclusive identity gather (slot_data[s]=data[leader])
		Cell *anchor = nullptr;
		pool<Cell *> cut_cells;
	};

	SigSpec emit_xbar(const Region &rg, const XbarCand &xb, const vector<SigBit> &leader,
	                  const vector<SigSpec> &slot, int cnt_w,
	                  const vector<SigSpec> *therm = nullptr)
	{
		Cell *anchor = rg.anchor;
		Cell *cell = anchor;
		int n = rg.n, a = xb.a, slot_w = xb.slot_w;
		SigSpec attr = sigmap(xb.attr_sig);
		bool use_therm = therm && GetSize(*therm) == n && n > 0 &&
		                 GetSize((*therm)[0]) >= xb.nb;

		// Shared f-table; each lane indexes it from its own attr (scan-independent).
		SigSpec table;
		for (int v = 0; v < (1 << a); v++)
			table.append(xb.ftab[v]);
		vector<SigSpec> f_lane(n);
		for (int i = 0; i < n; i++)
			f_lane[i] = emit_bmux(anchor, table, attr.extract(i * a, a), slot_w);

		// One-hot gather of precomputed f(attr[i]); default 0 when slot unused.
		SigSpec out;
		for (int s = 0; s < xb.nb; s++) {
			SigSpec sel, cases;
			for (int i = 0; i < n; i++) {
				SigBit eqs;
				if (use_therm)
					eqs = emit_therm_eq(anchor, (*therm)[i], s, GetSize((*therm)[i]));
				else
					eqs = emit_eq_const(anchor, slot[i], s, cnt_w);
				sel.append(emit_and(anchor, leader[i], eqs));
				cases.append(f_lane[i]);
			}
			Wire *y = module->addWire(NEW_ID2_SUFFIX("ffa_xbar_gather"), slot_w);
			module->addPmux(NEW_ID2_SUFFIX("ffa_xbar_gather_pmux"), Const(0, slot_w),
			                cases, sel, y, cell_src(anchor));
			cells_added++;
			out.append(SigSpec(y));
		}
		return out;
	}

	// Exclusive identity gather: slot_data[s] = data[leader at slot s]. Prefer
	// thermometer equality when available (avoids binary $eq on the critical
	// path). Emitted as a one-hot $pmux (default 0) — compact vs OR-of-ANDs
	// for wide payloads, and maps to a mux tree downstream.
	SigSpec emit_exclusive_gather(const Region &rg, const XbarCand &xb,
	                              const vector<SigBit> &grant, const vector<SigSpec> &slot,
	                              int cnt_w, const vector<SigSpec> *therm = nullptr)
	{
		Cell *anchor = rg.anchor;
		Cell *cell = anchor;
		int n = rg.n, a = xb.a, slots = xb.nb, slot_w = xb.slot_w;
		SigSpec attr = sigmap(xb.attr_sig);
		bool use_therm = therm && GetSize(*therm) == n && slots == rg.nb;
		SigSpec out;
		for (int s = 0; s < slots; s++) {
			SigSpec sel, cases;
			for (int l = 0; l < n; l++) {
				SigBit eqs;
				if (use_therm)
					eqs = emit_therm_eq(anchor, (*therm)[l], s, rg.nb);
				else
					eqs = emit_eq_const(anchor, slot[l], s, cnt_w);
				sel.append(emit_and(anchor, grant[l], eqs));
				cases.append(attr.extract(l * a, a));
			}
			Wire *y = module->addWire(NEW_ID2_SUFFIX("ffa_excl_gather"), slot_w);
			module->addPmux(NEW_ID2_SUFFIX("ffa_excl_gather_pmux"), Const(0, slot_w),
			                cases, sel, y, cell_src(anchor));
			cells_added++;
			out.append(SigSpec(y));
		}
		return out;
	}

	// ----------------------------------------------------------------
	// Candidate bus collection for a root cone.
	// ----------------------------------------------------------------
	// Candidate enable/broadcast buses: width-N buses whose every bit is an
	// internal (cone-cell-output) signal. The enable/broadcast lanes are
	// computed signals (e.g. valid & format), not the leaf categories, so
	// restricting to internal bits sidesteps the flood of wide intermediate
	// nets that otherwise swamps a generic wire-run sweep.
	void collect_lane_buses(const pool<Cell *> &cone_cells, int n,
	                        vector<BusCand> &width_n_buses)
	{
		pool<SigBit> internal_bits;
		for (auto c : cone_cells)
			for (auto &conn : c->connections())
				if (c->output(conn.first))
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							internal_bits.insert(bit);

		pool<SigSpec> seen;
		// Accept a bus bit if it is a cone-internal (computed) signal or a
		// primary input / undriven bit. The enable/broadcast lanes are usually
		// computed signals (e.g. valid & format), but some RTL drives the scan
		// straight from a top-level request port (e.g. lane_en), so input buses
		// must be admissible too. Inputs sort shallowest (depth 0) below, so they
		// survive the candidate cap ahead of the deep intermediate nets.
		auto all_internal_or_input = [&](const SigSpec &s) {
			for (auto bit : s)
				if (!bit.wire || (!internal_bits.count(bit) &&
				                  bit_to_driver.at(bit, nullptr) != nullptr))
					return false;
			return true;
		};
		auto add = [&](const SigSpec &sig, const std::string &nm) {
			SigSpec s = sigmap(sig);
			if (GetSize(s) != n || !sig_bus_ok(s) || !all_internal_or_input(s))
				return;
			if (!seen.insert(s).second)
				return;
			width_n_buses.push_back({s, nm, 0, 0});
		};

		for (auto w : module->wires())
			if (GetSize(w) == n)
				add(SigSpec(w), w->name.str());
		for (auto &bus : collect_cone_split_buses(internal_bits))
			if (bus.elem_width == 1 && bus.entries == n)
				add(bus.sig, bus.name);

		// Region inputs (enable/broadcast) sit just above the leaves; order
		// candidates shallowest-first so the deep intermediate nets of the
		// allocation network are only reached if the budget allows.
		dict<Cell *, int> depth = compute_cone_depths(cone_cells);
		auto bus_depth = [&](const SigSpec &s) {
			int d = 0;
			for (auto bit : s) {
				Cell *drv = bit_to_driver.at(bit, nullptr);
				if (drv != nullptr)
					d = std::max(d, depth.at(drv, 1 << 30));
			}
			return d;
		};
		std::stable_sort(width_n_buses.begin(), width_n_buses.end(),
		                 [&](const BusCand &a, const BusCand &b) {
		                     return bus_depth(a.sig) < bus_depth(b.sig);
		                 });
		const int max_en_bc = 24;
		if (GetSize(width_n_buses) > max_en_bc)
			width_n_buses.resize(max_en_bc);

		log_debug("    collect_lane_buses: %d width-%d internal bus(es) (capped)\n",
		          GetSize(width_n_buses), n);
		for (auto &b : width_n_buses)
			log_debug("      en/bc cand %s (depth %d)\n", b.name.c_str(), bus_depth(b.sig));
	}

	// ----------------------------------------------------------------
	// Try to match a dsel region rooted at `root_sig` (n lanes x field_w).
	// ----------------------------------------------------------------
	bool match_dsel(const SigSpec &root_sig, const std::string &root_name, int n, int field_w,
	                Region &out)
	{
		pool<Cell *> cone_cells;
		pool<SigBit> leaf_bits;
		int max_cone = std::max(512, max_n * 256);
		int max_leaf = max_n * max_n + max_n * 64 + max_n;
		if (!get_cone(root_sig, cone_cells, leaf_bits, max_cone, max_leaf))
			return false;
		if (cone_cells.empty())
			return false;

		log_debug("ffa: match_dsel root %s (n=%d, w=%d): cone %d cells, %d leaves\n",
		          root_name.c_str(), n, field_w, GetSize(cone_cells), GetSize(leaf_bits));

		vector<BusCand> lane_buses;
		collect_lane_buses(cone_cells, n, lane_buses);
		log_debug("  %d width-%d lane bus candidate(s)\n", GetSize(lane_buses), n);
		for (auto &b : lane_buses)
			log_debug("    lane bus %s\n", b.name.c_str());
		ConstEval ce(module);
		int64_t cone_est = GetSize(cone_cells) + 16;
		const int max_fp = 48;
		int fp = 0;

		// === Exclusive saturating first-fit (no category / broadcast) ===
		// Prefer a named width-n enable bus (e.g. \req): the dsel cone then
		// closes with no extra leaves, so the prefix-count leaves stay off the
		// launch-flop data words the identity gather reads.
		for (auto &en_bus : lane_buses) {
			if (fp >= max_fp || walk_exhausted() || eval_exhausted())
				break;
			pool<SigBit> en_bits = sig_bit_pool(en_bus.sig);
			pool<SigBit> extra_ex;
			if (!cut_cone_extra_leaves(root_sig, en_bits, GetSize(cone_cells) + 32, extra_ex, 8))
				continue;
			if (!extra_ex.empty())
				continue; // exclusive variant has no category leaves
			pool<SigBit> hit_ex;
			pool<Cell *> cut_ex;
			if (!cut_cone_walk(root_sig, en_bits, GetSize(cone_cells) + 32, &hit_ex, &cut_ex,
			                   &en_bits, &leaf_bits, &cone_cells)) {
				log_debug("  en=%s: exclusive cut not closed (%s)\n", en_bus.name.c_str(),
				          last_cut_fail.c_str());
				continue;
			}
			bool conflict_ex = false;
			for (auto bit : en_bits) {
				Cell *drv = bit_to_driver.at(bit, nullptr);
				if (drv != nullptr && cut_ex.count(drv)) { conflict_ex = true; break; }
			}
			if (conflict_ex)
				continue;
			for (int dir = 0; dir < 2; dir++) {
				if (fp >= max_fp || eval_exhausted())
					break;
				bool msb_first = (dir == 1);
				int nb = 0;
				if (!learn_exclusive_nb(ce, root_sig, n, field_w, en_bus.sig, msb_first,
				                        cone_est, nb))
					continue;
				fp++;
				bool m = fingerprint_dsel_exclusive(ce, root_sig, n, field_w, en_bus.sig,
				                                    msb_first, nb, cone_est);
				log_debug("  en=%s exclusive nb=%d %s: fingerprint %s\n", en_bus.name.c_str(),
				          nb, msb_first ? "MSB" : "LSB", m ? "MATCH" : "no");
				if (m) {
					out.dsel_sig = root_sig;
					out.dsel_name = root_name;
					out.n = n;
					out.field_w = field_w;
					out.en_sig = en_bus.sig;
					out.has_bc = false;
					out.coalesce = false;
					out.c = 0;
					out.exclusive = true;
					out.exclusive_and2 = false;
					out.nb = nb;
					out.msb_first = msb_first;
					out.dsel_cut_cells = cut_ex;
					find_anchor_driver(root_sig, out.anchor);
					return true;
				}
			}
		}

		// Fallback: reconstruct the enable as the AND of two leaf runs on the
		// launch flop (e.g. req = data_q[N-1:0] & data_q[2N-1:N]). Only tried
		// if a named enable bus did not match, so \req stays preferred.
		{
			auto pairs = pair_and2_leaf_runs(leaf_bits, n);
			for (auto &pr : pairs) {
				if (fp >= max_fp || walk_exhausted() || eval_exhausted())
					break;
				SigSpec en2;
				en2.append(pr.first);
				en2.append(pr.second);
				pool<SigBit> en_bits = sig_bit_pool(en2);
				pool<SigBit> hit_ex;
				pool<Cell *> cut_ex;
				if (!cut_cone_walk(root_sig, en_bits, GetSize(cone_cells) + 32, &hit_ex, &cut_ex,
				                   &en_bits, &leaf_bits, &cone_cells)) {
					log_debug("  en=and2(leaves): cut not closed (%s)\n", last_cut_fail.c_str());
					continue;
				}
				bool conflict_ex = false;
				for (auto bit : en_bits) {
					Cell *drv = bit_to_driver.at(bit, nullptr);
					if (drv != nullptr && cut_ex.count(drv)) { conflict_ex = true; break; }
				}
				if (conflict_ex)
					continue;
				for (int dir = 0; dir < 2; dir++) {
					if (fp >= max_fp || eval_exhausted())
						break;
					bool msb_first = (dir == 1);
					int nb = 0;
					if (!learn_exclusive_nb_and2(ce, root_sig, n, field_w, en2, msb_first,
					                             cone_est, nb))
						continue;
					fp++;
					bool m = fingerprint_dsel_exclusive_and2(ce, root_sig, n, field_w, en2,
					                                         msb_first, nb, cone_est);
					log_debug("  en=and2(leaves) exclusive nb=%d %s: fingerprint %s\n", nb,
					          msb_first ? "MSB" : "LSB", m ? "MATCH" : "no");
					if (m) {
						out.dsel_sig = root_sig;
						out.dsel_name = root_name;
						out.n = n;
						out.field_w = field_w;
						out.en_sig = en2;
						out.has_bc = false;
						out.coalesce = false;
						out.c = 0;
						out.exclusive = true;
						out.exclusive_and2 = true;
						out.nb = nb;
						out.msb_first = msb_first;
						out.dsel_cut_cells = cut_ex;
						find_anchor_driver(root_sig, out.anchor);
						return true;
					}
				}
			}
		}

		if (GetSize(lane_buses) < 1)
			return false;

		for (auto &en_bus : lane_buses) {
			if (fp >= max_fp || walk_exhausted() || eval_exhausted())
				break;
			pool<SigBit> en_bits = sig_bit_pool(en_bus.sig);

			// bc options: none, or each other 1-bit/lane bus.
			vector<const BusCand *> bc_opts;
			bc_opts.push_back(nullptr);
			for (auto &b : lane_buses)
				if (b.sig != en_bus.sig)
					bc_opts.push_back(&b);

			for (auto bc_bus : bc_opts) {
				if (fp >= max_fp || walk_exhausted() || eval_exhausted())
					break;

				pool<SigBit> allowed_eb = en_bits;
				if (bc_bus)
					for (auto bit : sig_bit_pool(bc_bus->sig))
						allowed_eb.insert(bit);

				// Find the category leaves: cut at (en,bc), gather extras.
				pool<SigBit> extra;
				if (!cut_cone_extra_leaves(root_sig, allowed_eb, GetSize(cone_cells) + 32,
				                           extra, n * max_cat_w + 8)) {
					log_debug("  en=%s bc=%s: too many extra leaves\n", en_bus.name.c_str(),
					          bc_bus ? bc_bus->name.c_str() : "-");
					continue;
				}
				if (extra.empty())
					continue;

				SigSpec cat_sig;
				int c = 0;
				vector<FieldKey> cat_keys;
				if (!group_lane_field(extra, n, cat_sig, c, &cat_keys)) {
					log_debug("  en=%s bc=%s: cat grouping failed (%d extra leaves)\n",
					          en_bus.name.c_str(), bc_bus ? bc_bus->name.c_str() : "-", GetSize(extra));
					continue;
				}
				if (c < 1 || c > max_cat_w)
					continue;
				if ((1 << c) > (1 << field_w))  // need ranks to fit the field
					continue;
				log_debug("  en=%s bc=%s: cat=%dx%d candidate\n", en_bus.name.c_str(),
				          bc_bus ? bc_bus->name.c_str() : "-", n, c);

				// Confirm the cut closes at exactly (en,bc,cat).
				pool<SigBit> allowed = allowed_eb;
				for (auto bit : sig_bit_pool(cat_sig))
					allowed.insert(bit);
				pool<SigBit> hit;
				pool<Cell *> cut_cells;
				if (!cut_cone_walk(root_sig, allowed, GetSize(cone_cells) + 32, &hit, &cut_cells,
				                   &allowed, &leaf_bits, &cone_cells)) {
					log_debug("  en=%s bc=%s cat=%dx%d: cut not closed (%s)\n", en_bus.name.c_str(),
					          bc_bus ? bc_bus->name.c_str() : "-", n, c, last_cut_fail.c_str());
					continue;
				}

				// Forced inputs must not be driven inside the cut cone.
				bool forced_conflict = false;
				for (auto bit : allowed) {
					Cell *drv = bit_to_driver.at(bit, nullptr);
					if (drv != nullptr && cut_cells.count(drv)) {
						forced_conflict = true;
						break;
					}
				}
				if (forced_conflict)
					continue;

				// Fingerprint both scan directions.
				for (int dir = 0; dir < 2; dir++) {
					if (fp >= max_fp || eval_exhausted())
						break;
					bool msb_first = (dir == 1);
					fp++;
					bool fpm = fingerprint_dsel(ce, root_sig, n, field_w, en_bus.sig,
					                     bc_bus ? bc_bus->sig : SigSpec(), bc_bus != nullptr,
					                     cat_sig, c, msb_first, cone_est);
					// Standard first-fit failed: try the enable-independent
					// forward-coalescing variant (no broadcast lane).
					bool coalesce = false;
					if (!fpm && bc_bus == nullptr) {
						fpm = fingerprint_dsel(ce, root_sig, n, field_w, en_bus.sig,
						                       SigSpec(), false, cat_sig, c, msb_first,
						                       cone_est, /*coalesce=*/true);
						coalesce = fpm;
					}
					log_debug("  en=%s bc=%s cat=%dx%d %s: fingerprint %s%s\n", en_bus.name.c_str(),
					          bc_bus ? bc_bus->name.c_str() : "-", n, c,
					          msb_first ? "MSB" : "LSB", fpm ? "MATCH" : "no",
					          coalesce ? " (coalesce)" : "");
					if (fpm) {
						out.dsel_sig = root_sig;
						out.dsel_name = root_name;
						out.n = n;
						out.field_w = field_w;
						out.en_sig = en_bus.sig;
						out.bc_sig = (!coalesce && bc_bus) ? bc_bus->sig : SigSpec();
						out.has_bc = (!coalesce && bc_bus != nullptr);
						out.coalesce = coalesce;
						out.cat_sig = cat_sig;
						out.c = c;
						out.msb_first = msb_first;
						out.cat_keys = cat_keys;
						out.dsel_cut_cells = cut_cells;
						find_anchor_driver(root_sig, out.anchor);
						return true;
					}
				}
			}
		}
		return false;
	}

	// Functional fingerprint of a candidate dsel region: drive (en,bc,cat) with
	// each generated test vector, ConstEval the root, and compare every lane's
	// evaluated rank against the closed-form first-fit reference
	// (compute_alloc_dir). Returns true iff all lanes match on every vector,
	// i.e. the region implements the first-fit dsel for the given direction.
	// Any eval failure or single mismatch rejects the candidate.
	bool fingerprint_dsel(ConstEval &ce, const SigSpec &root, int n, int field_w,
	                      const SigSpec &en_sig, const SigSpec &bc_sig, bool has_bc,
	                      const SigSpec &cat_sig, int c, bool msb_first, int64_t cone_est,
	                      bool coalesce = false)
	{
		int nval = 1 << c;
		vector<TestVector> vs = make_vectors(n, nval, has_bc);
		SigSpec en_s = sigmap(en_sig);
		SigSpec bc_s = has_bc ? sigmap(bc_sig) : SigSpec();
		SigSpec cat_s = sigmap(cat_sig);

		for (auto &tv : vs) {
			vector<std::pair<SigSpec, Const>> sets;
			sets.push_back({en_s, pack_lanes(tv.en, 1)});
			if (has_bc)
				sets.push_back({bc_s, pack_lanes(tv.bc, 1)});
			sets.push_back({cat_s, pack_lanes(tv.label, c)});

			Const res;
			if (!eval_root(ce, sets, root, res, cone_est))
				return false;

			AllocResult ar = coalesce
			                     ? compute_alloc_coalesce_dir(tv.en, tv.label, n, msb_first)
			                     : compute_alloc_dir(tv.en, tv.bc, tv.label, n, msb_first);
			for (int k = 0; k < n; k++) {
				int got = lane_val(res, k, field_w);
				int exp = ar.dsel[k] & ((1 << field_w) - 1);
				if (got != exp)
					return false;
			}
		}
		return true;
	}

	// ----------------------------------------------------------------
	// Exclusive-variant learn + fingerprint.
	// ----------------------------------------------------------------
	// Learn the slot budget nb: drive all lanes enabled and read the dsel
	// root. In priority order the granted lanes take ranks 0,1,2,...,nb-1 and
	// later lanes saturate to 0, so nb is the length of the leading 0,1,2,...
	// run. Returns false if the very first lane is nonzero (not exclusive).
	bool learn_exclusive_nb(ConstEval &ce, const SigSpec &root, int n, int field_w,
	                        const SigSpec &en_sig, bool msb_first, int64_t cone_est, int &nb)
	{
		vector<int> en(n, 1);
		vector<std::pair<SigSpec, Const>> sets;
		sets.push_back({sigmap(en_sig), pack_lanes(en, 1)});
		Const res;
		if (!eval_root(ce, sets, root, res, cone_est))
			return false;
		auto lane_of = [&](int p) { return msb_first ? (n - 1 - p) : p; };
		nb = n;
		for (int p = 0; p < n; p++) {
			int v = lane_val(res, lane_of(p), field_w);
			if (v != p) {
				nb = p;
				break;
			}
		}
		return nb >= 1 && nb <= (1 << field_w);
	}

	// Same, for the and2 enable (drive both run halves so every lane's AND
	// enable is asserted).
	bool learn_exclusive_nb_and2(ConstEval &ce, const SigSpec &root, int n, int field_w,
	                             const SigSpec &en_sig, bool msb_first, int64_t cone_est, int &nb)
	{
		vector<int> en(n, 1);
		vector<std::pair<SigSpec, Const>> sets;
		sets.push_back({sigmap(en_sig), pack_exclusive_and2(en, n)});
		Const res;
		if (!eval_root(ce, sets, root, res, cone_est))
			return false;
		auto lane_of = [&](int p) { return msb_first ? (n - 1 - p) : p; };
		nb = n;
		for (int p = 0; p < n; p++) {
			int v = lane_val(res, lane_of(p), field_w);
			if (v != p) {
				nb = p;
				break;
			}
		}
		return nb >= 1 && nb <= (1 << field_w);
	}

	// Fingerprint a candidate dsel region against the exclusive saturating
	// closed form for the given direction and learned nb.
	bool fingerprint_dsel_exclusive(ConstEval &ce, const SigSpec &root, int n, int field_w,
	                                const SigSpec &en_sig, bool msb_first, int nb,
	                                int64_t cone_est)
	{
		vector<vector<int>> vs = make_exclusive_vectors(n);
		SigSpec en_s = sigmap(en_sig);
		for (auto &e : vs) {
			vector<std::pair<SigSpec, Const>> sets;
			sets.push_back({en_s, pack_lanes(e, 1)});
			Const res;
			if (!eval_root(ce, sets, root, res, cone_est))
				return false;
			ExclResult ar = compute_alloc_exclusive_dir(e, n, nb, msb_first);
			for (int k = 0; k < n; k++) {
				int got = lane_val(res, k, field_w);
				int exp = ar.dsel[k] & ((1 << field_w) - 1);
				if (got != exp)
					return false;
			}
		}
		return true;
	}

	bool fingerprint_dsel_exclusive_and2(ConstEval &ce, const SigSpec &root, int n, int field_w,
	                                     const SigSpec &en_sig, bool msb_first, int nb,
	                                     int64_t cone_est)
	{
		vector<vector<int>> vs = make_exclusive_vectors(n);
		SigSpec en_s = sigmap(en_sig);
		for (auto &e : vs) {
			vector<std::pair<SigSpec, Const>> sets;
			sets.push_back({en_s, pack_exclusive_and2(e, n)});
			Const res;
			if (!eval_root(ce, sets, root, res, cone_est))
				return false;
			ExclResult ar = compute_alloc_exclusive_dir(e, n, nb, msb_first);
			for (int k = 0; k < n; k++) {
				int got = lane_val(res, k, field_w);
				int exp = ar.dsel[k] & ((1 << field_w) - 1);
				if (got != exp)
					return false;
			}
		}
		return true;
	}

	// Fingerprint a candidate done bus == grant[] for the exclusive region.
	bool fingerprint_done_exclusive(ConstEval &ce, const SigSpec &done_root, const Region &rg,
	                                int64_t cone_est)
	{
		int n = rg.n, nb = rg.nb;
		vector<vector<int>> vs = make_exclusive_vectors(n);
		SigSpec en_s = sigmap(rg.en_sig);
		for (auto &e : vs) {
			vector<std::pair<SigSpec, Const>> sets;
			if (rg.exclusive_and2)
				sets.push_back({en_s, pack_exclusive_and2(e, n)});
			else
				sets.push_back({en_s, pack_lanes(e, 1)});
			Const res;
			if (!eval_root(ce, sets, done_root, res, cone_est))
				return false;
			ExclResult ar = compute_alloc_exclusive_dir(e, n, nb, rg.msb_first);
			for (int l = 0; l < n; l++) {
				int got = (l < GetSize(res) && res[l] == State::S1) ? 1 : 0;
				if (got != ar.done[l])
					return false;
			}
		}
		return true;
	}

	// Deterministic per-(vector,lane) payload for the identity-gather probe.
	int gather_payload(int vidx, int lane, int a) const
	{
		uint64_t x = (uint64_t)(vidx * 2654435761u) ^ ((uint64_t)(lane + 1) * 0x9E3779B1u);
		x ^= x >> 13;
		x *= 0xff51afd7ed558ccdULL;
		x ^= x >> 33;
		uint64_t mask = (a >= 31) ? 0x7fffffffULL : ((1ULL << a) - 1);
		return (int)(x & mask);
	}

	// Fingerprint the exclusive identity gather: with (dsel,done) forced to
	// the reference allocation and per-lane data forced, slot s must equal
	// the data of the leader that took slot s (bit-for-bit), and 0 when no
	// leader took slot s. The enable is NOT forced: (dsel,done) are cut, so
	// the gather is a pure function of (dsel,done,data), and for the and2
	// enable the en leaves overlap the low data words -- forcing en here would
	// double-assign those bits, so we drive only (dsel,done,data).
	bool fingerprint_gather_exclusive(ConstEval &ce, const SigSpec &root, const Region &rg,
	                                  const SigSpec &dsel_sig, const SigSpec &done_sig,
	                                  bool has_done, const SigSpec &attr_sig, int a,
	                                  int slots, int slot_w, int64_t cone_est,
	                                  const char *name, const SigSpec &hold_q = SigSpec())
	{
		int n = rg.n, nb = rg.nb, field_w = rg.field_w;
		SigSpec dsel_s = sigmap(dsel_sig);
		SigSpec done_s = has_done ? sigmap(done_sig) : SigSpec();
		SigSpec attr_s = sigmap(attr_sig);
		SigSpec en_s = sigmap(rg.en_sig);

		vector<vector<int>> vs = make_exclusive_vectors(n);
		int vidx = 0;
		for (auto &e : vs) {
			vidx++;
			ExclResult ar = compute_alloc_exclusive_dir(e, n, nb, rg.msb_first);
			vector<int> data(n);
			for (int l = 0; l < n; l++)
				data[l] = gather_payload(vidx, l, a);

			vector<std::pair<SigSpec, Const>> sets;
			sets.push_back({dsel_s, pack_lanes(ar.dsel, field_w)});
			if (has_done)
				sets.push_back({done_s, pack_lanes(ar.done, 1)});
			else if (!rg.exclusive_and2)
				// No matched done bus: the gather derives done from the enable
				// internally, so force the enable too (safe only when it does
				// not overlap the data words -- i.e. not the and2 case).
				sets.push_back({en_s, pack_lanes(e, 1)});
			sets.push_back({attr_s, pack_lanes(data, a)});
			if (GetSize(hold_q) > 0)
				sets.push_back({hold_q, Const(State::S0, GetSize(hold_q))});

			Const res;
			if (!eval_root(ce, sets, root, res, cone_est)) {
				log_debug("  excl-gather %s: fingerprint eval failed\n", name);
				return false;
			}
			for (int s = 0; s < slots; s++) {
				int leader_lane = -1;
				for (int l = 0; l < n; l++)
					if (ar.done[l] && ar.dsel[l] == s) {
						leader_lane = l;
						break;
					}
				for (int b = 0; b < slot_w; b++) {
					bool got = (s * slot_w + b < GetSize(res)) &&
					           res[s * slot_w + b] == State::S1;
					bool exp = (leader_lane >= 0) && ((data[leader_lane] >> b) & 1);
					if (got != exp) {
						log_debug("  excl-gather %s: fingerprint mismatch slot %d bit %d\n",
						          name, s, b);
						return false;
					}
				}
			}
		}
		return true;
	}

	// ----------------------------------------------------------------
	// Try to match the xbar per-slot field gather sharing the region scan.
	// ----------------------------------------------------------------
	bool match_xbar(const Region &rg, const BusCand &cand, XbarCand &out)
	{
		int total_bits = GetSize(cand.sig);
		int field_w = rg.field_w;
		int nb = 1 << field_w;          // slot count = 2^W
		if (nb < 2 || total_bits % nb != 0)
			return false;
		int slot_w = total_bits / nb;
		if (slot_w < 1 || slot_w > 64) {
			log_debug("  xbar %s: slot_w=%d out of range\n", cand.name.c_str(), slot_w);
			return false;
		}

		SigSpec root = sigmap(cand.sig);
		pool<Cell *> cone_cells;
		pool<SigBit> leaf_bits;
		int max_cone = std::max(512, max_n * 256);
		int max_leaf = max_n * max_n + max_n * 64 + max_n;
		if (!get_cone(root, cone_cells, leaf_bits, max_cone, max_leaf)) {
			log_debug("  xbar %s: get_cone failed\n", cand.name.c_str());
			return false;
		}
		if (cone_cells.empty()) {
			log_debug("  xbar %s: empty cone\n", cand.name.c_str());
			return false;
		}

		// Cut at (en,bc); the remaining leaves are the per-lane attr field.
		pool<SigBit> allowed_eb = sig_bit_pool(rg.en_sig);
		if (rg.has_bc)
			for (auto bit : sig_bit_pool(rg.bc_sig))
				allowed_eb.insert(bit);
		pool<SigBit> extra;
		if (!cut_cone_extra_leaves(root, allowed_eb, GetSize(cone_cells) + 32,
		                           extra, rg.n * max_attr_w + 8)) {
			log_debug("  xbar %s: too many extra leaves on (en,bc) cut\n", cand.name.c_str());
			return false;
		}
		if (extra.empty()) {
			log_debug("  xbar %s: no extra leaves\n", cand.name.c_str());
			return false;
		}

		SigSpec attr_sig;
		int a = 0;
		vector<FieldKey> attr_keys;
		if (!group_lane_field(extra, rg.n, attr_sig, a, &attr_keys)) {
			log_debug("  xbar %s: attr grouping failed (%d extra leaves)\n",
			          cand.name.c_str(), GetSize(extra));
			return false;
		}
		if (a < rg.c || a > max_attr_w) {
			log_debug("  xbar %s: attr width %d out of range [%d,%d]\n",
			          cand.name.c_str(), a, rg.c, max_attr_w);
			return false;
		}
		// Bail before 2^a ConstEvals / emit when the product is too large.
		int64_t emit_bits = (int64_t)rg.n * (int64_t)nb * (int64_t)slot_w;
		int64_t ftab_bits = (int64_t)(1 << a) * (int64_t)slot_w;
		if (emit_bits > max_xbar_emit_bits || ftab_bits > max_xbar_emit_bits) {
			log_debug("  xbar %s: emit/ftab too large (emit_bits=%lld ftab_bits=%lld)\n",
			          cand.name.c_str(), (long long)emit_bits, (long long)ftab_bits);
			return false;
		}
		// ftab learn alone is 2^a evals; refuse if remaining eval budget cannot
		// cover that plus a small fingerprint margin.
		int64_t cone_est = GetSize(cone_cells) + 16;
		int64_t ftab_cost = (int64_t)(1 << a) * cone_est;
		if (eval_exhausted() || eval_budget < ftab_cost + 8 * cone_est) {
			log_debug("  xbar %s: eval budget too low for ftab (need ~%lld, have %lld)\n",
			          cand.name.c_str(), (long long)(ftab_cost + 8 * cone_est),
			          (long long)eval_budget);
			return false;
		}
		log_debug("  xbar %s: nb=%d slot_w=%d attr=%dx%d\n", cand.name.c_str(), nb, slot_w, rg.n, a);

		// Confirm closure at (en,bc,attr).
		pool<SigBit> allowed = allowed_eb;
		for (auto bit : sig_bit_pool(attr_sig))
			allowed.insert(bit);
		pool<SigBit> hit;
		pool<Cell *> cut_cells;
		if (!cut_cone_walk(root, allowed, GetSize(cone_cells) + 32, &hit, &cut_cells,
		                   &allowed, &leaf_bits, &cone_cells)) {
			log_debug("  xbar %s: cut not closed (%s)\n", cand.name.c_str(), last_cut_fail.c_str());
			return false;
		}
		for (auto bit : allowed) {
			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv != nullptr && cut_cells.count(drv)) {
				log_debug("  xbar %s: forced bit driven inside cone\n", cand.name.c_str());
				return false;
			}
		}

		// The attr field must be a superset of the category field (so the
		// scan's leadership and the xbar gather see consistent lanes).
		// (cat keys identify wire/offset; verify each is present in attr.)
		// We do not strictly require this for correctness (the fingerprint
		// is authoritative), but it weeds out unrelated buses cheaply.

		ConstEval ce(module);

		// Learn f(v): force lane 0 (priority E0) the sole leader with attr=v.
		int e0_lane = rg.msb_first ? (rg.n - 1) : 0;
		vector<Const> ftab(1 << a);
		SigSpec en_s = sigmap(rg.en_sig);
		SigSpec bc_s = rg.has_bc ? sigmap(rg.bc_sig) : SigSpec();
		SigSpec attr_s = sigmap(attr_sig);
		SigSpec slot0 = root.extract(0, slot_w);
		for (int v = 0; v < (1 << a); v++) {
			vector<int> en(rg.n, 0), bc(rg.n, 0), attr(rg.n, 0);
			en[e0_lane] = 1;
			attr[e0_lane] = v;
			vector<std::pair<SigSpec, Const>> sets;
			sets.push_back({en_s, pack_lanes(en, 1)});
			if (rg.has_bc)
				sets.push_back({bc_s, pack_lanes(bc, 1)});
			sets.push_back({attr_s, pack_lanes(attr, a)});
			Const res;
			if (!eval_root(ce, sets, slot0, res, cone_est)) {
				log_debug("  xbar %s: ftab learn failed at v=%d\n", cand.name.c_str(), v);
				return false;
			}
			ftab[v] = res;
		}

		// Fingerprint with single-leader vectors only. Multi-leader ConstEval of
		// the serial taken/done cone is unreliable on some elaborations (X-OR
		// pollution); leadership/slot assignment is already proven by the dsel
		// fingerprint, and ftab learning covers f(attr). Check only the occupied
		// slot: unused slots often eval to X/1 under partial assigns even when
		// the RTL zeros them, so requiring exp=0 there rejects true matches.
		int nval = 1 << a;
		vector<TestVector> vs = make_vectors(rg.n, nval, rg.has_bc);
		for (auto &tv : vs) {
			vector<int> catlab(rg.n);
			for (int k = 0; k < rg.n; k++)
				catlab[k] = cat_from_attr(tv.label[k], rg.cat_keys, attr_keys);
			AllocResult ar = rg.coalesce
			                     ? compute_alloc_coalesce_dir(tv.en, catlab, rg.n, rg.msb_first)
			                     : compute_alloc_dir(tv.en, tv.bc, catlab, rg.n, rg.msb_first);
			if (ar.M > 1)
				continue;

			vector<int> attr_lab(rg.n, 0);
			for (int k = 0; k < rg.n; k++)
				if (ar.leader[k])
					attr_lab[k] = tv.label[k];

			vector<std::pair<SigSpec, Const>> sets;
			sets.push_back({en_s, pack_lanes(tv.en, 1)});
			if (rg.has_bc)
				sets.push_back({bc_s, pack_lanes(tv.bc, 1)});
			sets.push_back({attr_s, pack_lanes(attr_lab, a)});
			Const res;
			if (!eval_root(ce, sets, root, res, cone_est)) {
				log_debug("  xbar %s: eval failed during fingerprint\n", cand.name.c_str());
				return false;
			}

			for (int s = 0; s < nb; s++) {
				int leader_lane = -1;
				for (int i = 0; i < rg.n; i++)
					if (ar.leader[i] && ar.slot[i] == s) { leader_lane = i; break; }
				if (leader_lane < 0)
					continue;
				for (int b = 0; b < slot_w; b++) {
					bool got = (s * slot_w + b < GetSize(res)) && res[s * slot_w + b] == State::S1;
					const Const &fv = ftab[tv.label[leader_lane]];
					bool exp = (b < GetSize(fv)) && fv[b] == State::S1;
					if (got != exp) {
						log_debug("  xbar %s: fingerprint mismatch slot %d bit %d\n",
						          cand.name.c_str(), s, b);
						return false;
					}
				}
			}
		}
		log_debug("  xbar %s: MATCH\n", cand.name.c_str());

		out.sig = root;
		out.name = cand.name;
		out.nb = nb;
		out.slot_w = slot_w;
		out.attr_sig = attr_sig;
		out.a = a;
		out.ftab = ftab;
		out.attr_keys = attr_keys;
		out.cut_cells = cut_cells;
		find_anchor_driver(root, out.anchor);
		return true;
	}

	// Map an attr label value to its category label value, using the shared
	// (id,offset) keys: cat bit cb corresponds to the attr bit whose key
	// matches cat_keys[cb].
	int cat_from_attr(int attr_val, const vector<FieldKey> &cat_keys,
	                  const vector<FieldKey> &attr_keys)
	{
		int catval = 0;
		for (int cb = 0; cb < GetSize(cat_keys); cb++)
			for (int b = 0; b < GetSize(attr_keys); b++)
				if (attr_keys[b] == cat_keys[cb]) {
					if ((attr_val >> b) & 1)
						catval |= 1 << cb;
					break;
				}
		return catval;
	}

	// ----------------------------------------------------------------
	// Exclusive-variant enable reconstruction and identity gather.
	// ----------------------------------------------------------------
	bool is_gather_ff(Cell *c)
	{
		return is_clocked_ff(c);
	}

	// Reconstruct the enable as the AND of two n-bit leaf runs. The common
	// case is a contiguous 2n-bit (or longer) run on the launch flop (e.g.
	// req = data_q[N-1:0] & data_q[2N-1:N]) split into halves; pairs of
	// distinct n-bit runs are also offered. Runs come from the dsel cone
	// leaves. Longer-than-2n runs yield aligned 2n windows (capped) so a
	// wide flop Q that also feeds payload muxes still yields the enable pair.
	vector<std::pair<SigSpec, SigSpec>> pair_and2_leaf_runs(const pool<SigBit> &leaf_bits, int n)
	{
		vector<std::pair<SigSpec, SigSpec>> pairs;
		std::map<Wire *, std::set<int>> wire_offsets;
		for (auto b : leaf_bits)
			if (b.wire)
				wire_offsets[b.wire].insert(b.offset);
		struct Run { Wire *w; int start; int len; };
		vector<Run> runs;
		for (auto &kv : wire_offsets) {
			Wire *w = kv.first;
			int run_start = -1, prev = -2;
			for (int o : kv.second) {
				if (o != prev + 1) {
					if (run_start >= 0)
						runs.push_back({w, run_start, prev - run_start + 1});
					run_start = o;
				}
				prev = o;
			}
			if (run_start >= 0)
				runs.push_back({w, run_start, prev - run_start + 1});
		}
		auto push_halves = [&](Wire *w, int start) {
			SigSpec a, b;
			for (int i = 0; i < n; i++)
				a.append(SigBit(w, start + i));
			for (int i = 0; i < n; i++)
				b.append(SigBit(w, start + n + i));
			pairs.push_back({a, b});
		};
		// Split contiguous >=2n runs into low/high halves (aligned windows).
		const int max_windows = 4;
		for (auto &r : runs) {
			if (r.len < 2 * n)
				continue;
			int windows = 0;
			for (int off = 0; off + 2 * n <= r.len && windows < max_windows; off += n) {
				push_halves(r.w, r.start + off);
				windows++;
				if (GetSize(pairs) >= 16)
					return pairs;
			}
		}
		// Pairs of distinct n-runs.
		vector<SigSpec> nruns;
		for (auto &r : runs) {
			if (r.len < n)
				continue;
			// Exact n-run, or aligned n-windows from a longer run (capped).
			int lim = (r.len == n) ? 1 : std::min(max_windows, r.len / n);
			for (int w = 0; w < lim; w++) {
				SigSpec s;
				for (int i = 0; i < n; i++)
					s.append(SigBit(r.w, r.start + w * n + i));
				nruns.push_back(s);
			}
		}
		for (int i = 0; i < GetSize(nruns); i++)
			for (int j = i + 1; j < GetSize(nruns); j++) {
				pairs.push_back({nruns[i], nruns[j]});
				if (GetSize(pairs) >= 16)
					return pairs;
			}
		return pairs;
	}

	// Find a width-n bus that equals the exclusive grant/done vector.
	bool match_exclusive_done(const Region &rg, SigSpec &done_sig)
	{
		int n = rg.n;
		ConstEval ce(module);
		vector<SigSpec> cands;
		pool<SigSpec> seen;
		SigSpec en_map = sigmap(rg.en_sig);
		SigSpec dsel_map = sigmap(rg.dsel_sig);
		auto add = [&](const SigSpec &raw) {
			SigSpec s = sigmap(raw);
			if (GetSize(s) != n || !sig_bus_ok(s))
				return;
			if (s == dsel_map || s == en_map)
				return;
			if (root_claimed(s))
				return;
			if (!seen.insert(s).second)
				return;
			cands.push_back(raw);
		};
		for (auto w : module->wires())
			if (GetSize(w) == n)
				add(SigSpec(w));
		for (auto c : module->cells())
			if (is_gather_ff(c) && c->hasPort(ID::D) && GetSize(c->getPort(ID::D)) == n)
				add(c->getPort(ID::D));
		vector<Wire *> all;
		for (auto w : module->wires())
			all.push_back(w);
		for (auto &bus : collect_split_buses(all))
			if (bus.entries == n && bus.elem_width == 1)
				add(bus.sig);

		pool<SigBit> allowed = sig_bit_pool(rg.en_sig);
		int tried = 0;
		for (auto &s : cands) {
			if (tried >= 16 || walk_exhausted() || eval_exhausted())
				break;
			pool<Cell *> cone_cells;
			pool<SigBit> leaf_bits;
			int max_cone = std::max(512, max_n * 256);
			int max_leaf = max_n * max_n + max_n * 64 + max_n;
			if (!get_cone(s, cone_cells, leaf_bits, max_cone, max_leaf))
				continue;
			if (cone_cells.empty())
				continue;
			pool<SigBit> extra;
			if (!cut_cone_extra_leaves(s, allowed, GetSize(cone_cells) + 32, extra, 8))
				continue;
			if (!extra.empty())
				continue;
			tried++;
			int64_t cone_est = GetSize(cone_cells) + 16;
			if (fingerprint_done_exclusive(ce, s, rg, cone_est)) {
				done_sig = s;
				return true;
			}
		}
		return false;
	}

	// Candidate identity-gather roots: per-slot flop-D packs grouped by the
	// register-name stem (so lane_done_o_reg is not mixed with the
	// slot_data_o_reg[*] array), plus split-array buses of nb equal-width
	// elements (bypassing the dsel-root max_field_w cap).
	struct GatherCand {
		SigSpec sig;
		std::string name;
		int slots = 0;
		int slot_w = 0;
		SigSpec hold_sig; // per-slot FF-Q hold bus (slot-major), for compaction
	};
	vector<GatherCand> collect_exclusive_gather_cands(int nb)
	{
		vector<GatherCand> cands;
		pool<SigSpec> seen;
		auto add = [&](const SigSpec &sig, const std::string &nm, int slots, int slot_w) {
			if (slots < 1 || slot_w < 1 || slot_w > max_gather_w)
				return;
			SigSpec s = sigmap(sig);
			if (!sig_bus_ok(s) || root_claimed(s))
				return;
			if (!seen.insert(s).second)
				return;
			cands.push_back({sig, nm, slots, slot_w, SigSpec()});
		};

		std::map<std::string, vector<std::pair<int, Cell *>>> ff_groups;
		for (auto c : module->cells()) {
			if (!is_gather_ff(c) || !c->hasPort(ID::Q) || !c->hasPort(ID::D))
				continue;
			SigSpec q = c->getPort(ID::Q);
			if (q.empty() || !q[0].wire)
				continue;
			std::string base;
			int idx = -1;
			if (parse_indexed_port_name(q[0].wire, base, idx))
				ff_groups[base].push_back({idx, c});
			else
				ff_groups[q[0].wire->name.str()].push_back({0, c});
		}
		for (auto &kv : ff_groups) {
			auto entries = kv.second;
			std::sort(entries.begin(), entries.end(),
			          [](const std::pair<int, Cell *> &a, const std::pair<int, Cell *> &b) {
			              return a.first < b.first;
			          });
			int slot_w = GetSize(entries.front().second->getPort(ID::D));
			bool ok = true;
			for (auto &e : entries)
				if (GetSize(e.second->getPort(ID::D)) != slot_w) {
					ok = false;
					break;
				}
			if (!ok)
				continue;
			int slots = GetSize(entries);
			SigSpec pack;
			for (auto &e : entries)
				pack.append(e.second->getPort(ID::D));
			if (slots == nb)
				add(pack, stringf("gather_ff[%s]", kv.first.c_str()), slots, slot_w);
			else if (slots == 1 && nb > 1 && slot_w % nb == 0) {
				// Single wide FF: Verific often packs Q as
				// {slot[0], slot[1], ...} (slot0 in the MSBs). Fingerprint
				// expects LSB-first slot packing, so reverse slot chunks when
				// the MSB chunk is the lowest-index slot_* wire.
				int sw = slot_w / nb;
				SigSpec d = entries.front().second->getPort(ID::D);
				SigSpec q = entries.front().second->getPort(ID::Q);
				bool msb_slot0 = false;
				if (GetSize(q) == GetSize(d) && GetSize(q) >= sw) {
					int best_idx = 1 << 30;
					int best_pos = -1;
					for (int pos = 0; pos < GetSize(q); pos += sw) {
						if (!q[pos].wire)
							continue;
						std::string qb;
						int qi = -1;
						if (!parse_indexed_port_name(q[pos].wire, qb, qi))
							continue;
						if (qi < best_idx) {
							best_idx = qi;
							best_pos = pos;
						}
					}
					// Lowest slot index sits in the MSB chunk (near GetSize-sw).
					msb_slot0 = (best_pos >= GetSize(q) - sw);
				}
				SigSpec ordered;
				if (msb_slot0) {
					for (int s = 0; s < nb; s++) {
						int hi = GetSize(d) - s * sw;
						ordered.append(d.extract(hi - sw, sw));
					}
				} else {
					ordered = d;
				}
				add(ordered, stringf("gather_ff[%s]", kv.first.c_str()), nb, sw);
			}
		}

		vector<Wire *> all;
		for (auto w : module->wires())
			all.push_back(w);
		for (auto &bus : collect_split_buses(all)) {
			if (bus.entries != nb)
				continue;
			if (bus.elem_width < 1 || bus.elem_width > max_gather_w)
				continue;
			add(bus.sig, bus.name, bus.entries, bus.elem_width);
		}

		if (GetSize(cands) > max_gather_cands)
			cands.resize(max_gather_cands);
		return cands;
	}

	// Try to match an exclusive identity gather rooted at `cand`. The gather
	// cone is cut at (en, dsel, optional done); the remaining leaves are the
	// per-lane data payloads. slot s must reproduce, bit-for-bit, the payload
	// of the lane that took slot s.
	bool match_exclusive_gather(const Region &rg, const GatherCand &cand,
	                            const SigSpec &done_sig, bool has_done, XbarCand &out)
	{
		int slots = cand.slots;
		int slot_w = cand.slot_w;
		if (slot_w < 1 || slot_w > max_gather_w) {
			log_debug("  excl-gather %s: slot_w=%d out of range\n", cand.name.c_str(), slot_w);
			return false;
		}
		SigSpec root = sigmap(cand.sig);
		pool<Cell *> cone_cells;
		pool<SigBit> leaf_bits;
		int max_cone = std::max(512, max_n * 256);
		int max_leaf = max_n * max_n + max_n * 64 + max_n;
		if (!get_cone(root, cone_cells, leaf_bits, max_cone, max_leaf))
			return false;
		if (cone_cells.empty())
			return false;

		pool<SigBit> allowed = sig_bit_pool(rg.en_sig);
		for (auto bit : sig_bit_pool(rg.dsel_sig))
			allowed.insert(bit);
		if (has_done)
			for (auto bit : sig_bit_pool(done_sig))
				allowed.insert(bit);
		// Pre-opt $dff hold muxes feed Q back into D; cut those Q bits so they
		// are not mistaken for payload attrs (opt rewrites them to $dffe).
		SigSpec hold_q;
		{
			pool<SigBit> root_bits = sig_bit_pool(root);
			pool<SigBit> hold_seen;
			for (auto c : module->cells()) {
				if (!is_gather_ff(c) || !c->hasPort(ID::D) || !c->hasPort(ID::Q))
					continue;
				bool overlaps = false;
				for (auto bit : sigmap(c->getPort(ID::D)))
					if (root_bits.count(bit)) {
						overlaps = true;
						break;
					}
				if (!overlaps)
					continue;
				for (auto bit : sigmap(c->getPort(ID::Q)))
					if (bit.wire && hold_seen.insert(bit).second) {
						allowed.insert(bit);
						hold_q.append(bit);
					}
			}
		}

		pool<SigBit> extra;
		if (!cut_cone_extra_leaves(root, allowed, GetSize(cone_cells) + 32, extra,
		                           rg.n * max_gather_w + 8)) {
			log_debug("  excl-gather %s: too many extra leaves\n", cand.name.c_str());
			return false;
		}
		// attr = extra leaves, plus the and2 enable leaves (the low data words,
		// which were cut above but belong to lanes 0/1's payload).
		pool<SigBit> attr_bits = extra;
		if (rg.exclusive_and2)
			for (auto bit : sig_bit_pool(rg.en_sig))
				attr_bits.insert(bit);

		SigSpec attr_sig;
		int a = 0;
		vector<FieldKey> attr_keys;
		if (!group_lane_field(attr_bits, rg.n, attr_sig, a, &attr_keys)) {
			log_debug("  excl-gather %s: attr grouping failed (%d bits)\n",
			          cand.name.c_str(), GetSize(attr_bits));
			return false;
		}
		if (a != slot_w) {
			log_debug("  excl-gather %s: attr width %d != slot_w %d\n",
			          cand.name.c_str(), a, slot_w);
			return false;
		}

		pool<SigBit> allowed2 = allowed;
		for (auto bit : sig_bit_pool(attr_sig))
			allowed2.insert(bit);
		pool<SigBit> hit;
		pool<Cell *> cut_cells;
		if (!cut_cone_walk(root, allowed2, GetSize(cone_cells) + 32, &hit, &cut_cells,
		                   &allowed2, &leaf_bits, &cone_cells)) {
			log_debug("  excl-gather %s: cut not closed (%s)\n", cand.name.c_str(),
			          last_cut_fail.c_str());
			return false;
		}
		for (auto bit : allowed2) {
			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv != nullptr && cut_cells.count(drv)) {
				log_debug("  excl-gather %s: cut not closed (forced bit driven inside cone)\n",
				          cand.name.c_str());
				return false;
			}
		}

		ConstEval ce(module);
		int64_t cone_est = GetSize(cone_cells) + 16;
		// Hold-Q leaves must be forced for ConstEval; value is don't-care when
		// the update mux selects the new payload (identity / fingerprint cases).
		auto push_hold_q = [&](vector<std::pair<SigSpec, Const>> &sets) {
			if (GetSize(hold_q) > 0)
				sets.push_back({hold_q, Const(State::S0, GetSize(hold_q))});
		};

		// Identity probe: priority-E0 sole leader (slot 0) with known payload.
		int e0_lane = rg.msb_first ? (rg.n - 1) : 0;
		SigSpec dsel_s = sigmap(rg.dsel_sig);
		SigSpec done_s = has_done ? sigmap(done_sig) : SigSpec();
		SigSpec attr_s = sigmap(attr_sig);
		SigSpec en_s = sigmap(rg.en_sig);
		for (int probe = 0; probe < 3; probe++) {
			vector<int> en(rg.n, 0), data(rg.n, 0), dsel(rg.n, 0), done(rg.n, 0);
			en[e0_lane] = 1;
			done[e0_lane] = 1; // dsel[e0] = 0 (rank 0)
			int pv = (probe == 0) ? ((a >= 31) ? 0x7fffffff : ((1 << a) - 1))
			       : (probe == 1) ? gather_payload(101, e0_lane, a)
			                      : (a >= 2 ? 2 : 1);
			data[e0_lane] = pv;
			vector<std::pair<SigSpec, Const>> sets;
			sets.push_back({dsel_s, pack_lanes(dsel, rg.field_w)});
			if (has_done)
				sets.push_back({done_s, pack_lanes(done, 1)});
			else if (!rg.exclusive_and2)
				sets.push_back({en_s, pack_lanes(en, 1)});
			sets.push_back({attr_s, pack_lanes(data, a)});
			push_hold_q(sets);
			Const res;
			if (!eval_root(ce, sets, root, res, cone_est)) {
				log_debug("  excl-gather %s: identity probe eval failed\n", cand.name.c_str());
				return false;
			}
			for (int b = 0; b < slot_w; b++) {
				bool got = (b < GetSize(res)) && res[b] == State::S1;
				bool exp = (pv >> b) & 1;
				if (got != exp) {
					log_debug("  excl-gather %s: identity probe mismatch bit %d\n",
					          cand.name.c_str(), b);
					return false;
				}
			}
		}

		if (!fingerprint_gather_exclusive(ce, root, rg, rg.dsel_sig, done_sig, has_done,
		                                  attr_sig, a, slots, slot_w, cone_est,
		                                  cand.name.c_str(), hold_q))
			return false;

		log_debug("  excl-gather %s: MATCH (identity, slot_w=%d)\n", cand.name.c_str(), slot_w);
		out.sig = root;
		out.name = cand.name;
		out.nb = slots;
		out.slot_w = slot_w;
		out.attr_sig = attr_sig;
		out.a = a;
		out.attr_keys = attr_keys;
		out.identity = true;
		out.cut_cells = cut_cells;
		find_anchor_driver(root, out.anchor);
		return true;
	}

	// Drive `new_val` onto the cell-driven bits of `root` (bit-aligned),
	// leaving folded-constant / undriven bits untouched (they already hold
	// the correct value and are not on the deep path). Returns the number of
	// bits actually re-driven.
	int connect_driven(const SigSpec &root, const SigSpec &new_val, Cell *anchor,
	                   const char *suffix)
	{
		log_assert(GetSize(root) == GetSize(new_val));
		SigSpec lhs, rhs;
		for (int i = 0; i < GetSize(root); i++) {
			SigBit rb = sigmap(root[i]);
			if (rb.wire && bit_to_driver.at(rb, nullptr) != nullptr) {
				lhs.append(root[i]);
				rhs.append(new_val[i]);
			}
		}
		if (GetSize(lhs) == 0)
			return 0;
		disconnect_root(lhs, anchor, suffix);
		module->connect(lhs, rhs);
		return GetSize(lhs);
	}

	// ----------------------------------------------------------------
	// Collect root candidates: per-lane split buses (entries in range).
	// ----------------------------------------------------------------
	struct RootSplit {
		SigSpec sig;
		std::string name;
		int n, elem;
	};
	vector<RootSplit> collect_split_roots()
	{
		vector<RootSplit> roots;
		vector<Wire *> all;
		for (auto w : module->wires())
			all.push_back(w);
		for (auto &bus : collect_split_buses(all)) {
			if (bus.entries < min_n || bus.entries > max_n)
				continue;
			if (bus.elem_width < 1 || bus.elem_width > max_field_w)
				continue;
			// Keep the raw (un-sigmapped) wire bits so the root stays
			// drivable; some field bits may fold to constants (e.g. the
			// always-zero MSB of an xbar entry) and only the cell-driven
			// bits get re-driven later. So we do NOT require sig_bus_ok
			// (which would reject any constant-folded bit); the split-bus
			// bits are real wire bits by construction. We only require at
			// least one cell-driven bit so pure input ports are skipped.
			bool raw_ok = true;
			for (auto bit : bus.sig)
				if (!bit.wire) {
					raw_ok = false;
					break;
				}
			if (!raw_ok)
				continue;
			bool any_driven = false;
			for (auto bit : sigmap(bus.sig))
				if (bit.wire && bit_to_driver.at(bit, nullptr) != nullptr) {
					any_driven = true;
					break;
				}
			if (!any_driven)
				continue;
			roots.push_back({bus.sig, bus.name, bus.entries, bus.elem_width});

			// Root padding: Verific drops always-zero low lanes (e.g.
			// lane_sel[0], which is rank 0 == 0), leaving a split bus that
			// starts at a nonzero base index. Offer a full n-lane root with the
			// missing low lanes padded to constant 0 (the exclusive closed form
			// assigns rank 0 -> 0 there, so the padded lanes fingerprint clean).
			if (bus.sig[0].wire) {
				std::string base;
				int base_index = -1;
				if (parse_indexed_port_name(bus.sig[0].wire, base, base_index) &&
				    base_index >= 1 && base_index <= 2) {
					int padded_n = bus.entries + base_index;
					if (padded_n >= min_n && padded_n <= max_n) {
						SigSpec padded(State::S0, base_index * bus.elem_width);
						padded.append(bus.sig);
						roots.push_back({padded, bus.name, padded_n, bus.elem_width});
					}
				}
			}
		}
		// widest fields first (real index buses are the deep ones)
		std::stable_sort(roots.begin(), roots.end(),
		                 [](const RootSplit &a, const RootSplit &b) { return a.n > b.n; });
		return roots;
	}

	// ================================================================
	// Gather-rooted anchor.
	//
	// The dsel-rooted path above needs an explicit per-lane rank bus to
	// anchor on. Some RTL never materializes one: the first-fit result is
	// consumed only as a per-slot DATA gather (slot_data[s] = data[the s-th
	// enabled lane in priority order]). Here we anchor directly on the
	// gather. The scan/emit machinery is shared with the exclusive dsel
	// path; only the anchor, region reconstruction and fingerprint differ.
	// ================================================================
	// A reconstructed per-lane enable factor: `bits` holds the n lane bits
	// (lane-major, possibly gathered through an affine index/bit stride) and
	// `neg` marks a term that is inverted before the AND. The lane enable is
	// en[k] = AND_t (neg_t ? !bits_t[k] : bits_t[k]).
	struct EnTerm {
		SigSpec bits;
		bool neg = false;
		std::string name;
	};

	struct GatherRegion {
		SigSpec en_sig;   // n 1-bit lane enables (the "avail" bus)
		vector<EnTerm> en_terms; // composite enable factors (compacted path)
		int n = 0;
		int nb = 0;       // slot budget == number of gather slots
		bool msb_first = false;
		SigSpec attr_sig; // lane-major per-lane payload (n * slot_w bits)
		int slot_w = 0;
		vector<FieldKey> attr_keys;
		SigSpec gather_sig; // the matched slot-major gather output (nb * slot_w)
		std::string name;
		pool<Cell *> cut_cells;
		Cell *anchor = nullptr;
		// Entry-side compaction: the slots are not read directly by index s,
		// but through a per-slot "select" bus sel[j] that itself forms a
		// second exclusive first-fit (the j-th ungated slot reads scan slot
		// popcount(sel[<j])). Empty when the gather is read by direct index.
		SigSpec sel_sig;  // nb 1-bit entry-select enables
		bool sel_compl = false; // active entry == !sel_sig[j] (e.g. sel==hit)
		bool sel_rev = false; // sel_sig bit for entry j is at index nb-1-j
		bool ent_msb_first = false; // entry-side scan direction
		SigSpec hold_sig; // nb*slot_w slot-major hold value (FF-Q) when no lane
		bool compacted = false;
		// When true the matched root still carries the per-entry active gate
		// (inactive entry -> hold), so the model/emit gate the drawn slot by
		// act[j]. When false the gate is external (already peeled), so an
		// inactive entry's ungated draw is a don't-care discarded downstream.
		bool ent_gated = false;
		// Guard leaves pinned to the allocation-active branch during the
		// fingerprint (FSM case select, per-slot guard mux selects). Not
		// re-driven by the rewrite: only the isolated alloc sub-node is.
		vector<std::pair<SigSpec, Const>> guard_sets;
		SigSpec hold_q;   // pre-opt $dff hold-mux Q feedback leaves (forced 0)
	};

	// Deterministic per-(vector,slot) payload for the gather-rooted probe;
	// distinct namespace from gather_payload so a data leaf that also feeds
	// the enable cannot alias its own value across the two roles.
	int gather_root_payload(int vidx, int lane, int a) const
	{
		uint64_t x = (uint64_t)(vidx * 0x27d4eb2fu) ^ ((uint64_t)(lane + 1) * 0x165667b1u);
		x ^= x >> 15;
		x *= 0xd6e8feb86659fd93ULL;
		x ^= x >> 32;
		uint64_t mask = (a >= 31) ? 0x7fffffffULL : ((1ULL << a) - 1);
		return (int)(x & mask);
	}

	// Fingerprint the gather-rooted region: with (en, data) forced (and any
	// guard leaves pinned to the allocation-active branch), slot s of `root`
	// must equal the payload of the lane that took slot s in the exclusive
	// first-fit, and 0 when no lane took slot s. Returns true iff every
	// slot/bit matches on every structured enable vector.
	bool fingerprint_gather_rooted(ConstEval &ce, const SigSpec &root,
	                               const GatherRegion &gr, int64_t cone_est,
	                               const char *name)
	{
		int n = gr.n, nb = gr.nb, slot_w = gr.slot_w, a = gr.slot_w;
		SigSpec en_s = sigmap(gr.en_sig);
		SigSpec attr_s = sigmap(gr.attr_sig);
		vector<vector<int>> vs = make_exclusive_vectors(n);
		int vidx = 0;
		for (auto &e : vs) {
			vidx++;
			ExclResult ar = compute_alloc_exclusive_dir(e, n, nb, gr.msb_first);
			vector<int> data(n);
			for (int l = 0; l < n; l++)
				data[l] = gather_root_payload(vidx, l, a);
			vector<std::pair<SigSpec, Const>> sets = gr.guard_sets;
			sets.push_back({en_s, pack_lanes(e, 1)});
			sets.push_back({attr_s, pack_lanes(data, a)});
			if (GetSize(gr.hold_q) > 0)
				sets.push_back({gr.hold_q, Const(State::S0, GetSize(gr.hold_q))});
			Const res;
			if (!eval_root(ce, sets, root, res, cone_est)) {
				log_debug("  gather-root %s: fingerprint eval failed (vidx %d)\n", name, vidx);
				return false;
			}
			for (int s = 0; s < nb; s++) {
				int leader_lane = -1;
				for (int l = 0; l < n; l++)
					if (ar.done[l] && ar.dsel[l] == s) { leader_lane = l; break; }
				for (int b = 0; b < slot_w; b++) {
					bool got = (s * slot_w + b < GetSize(res)) &&
					           res[s * slot_w + b] == State::S1;
					bool exp = (leader_lane >= 0) && ((data[leader_lane] >> b) & 1);
					if (got != exp) {
						log_debug("  gather-root %s: mismatch slot %d bit %d (vidx %d)\n",
						          name, s, b, vidx);
						return false;
					}
				}
			}
		}
		return true;
	}

	// Entry-side compaction rank: number of active entries strictly before j
	// in entry priority order. `act[j]` is the per-entry active mask.
	vector<int> entry_ranks(const vector<int> &act, int nb, bool ent_msb) const
	{
		vector<int> erank(nb, 0);
		int acc = 0;
		for (int p = 0; p < nb; p++) {
			int j = ent_msb ? (nb - 1 - p) : p;
			erank[j] = acc;
			acc += act[j] ? 1 : 0;
		}
		return erank;
	}

	// Fingerprint the entry-side-compacted gather. With (en, sel, data, hold)
	// forced (plus any pinned guard leaves), entry-slot j of `root` must equal
	// the payload of the lane drawn by the popcount(active[<j])-th active
	// entry, or the FF-Q hold value when that lane-slot has no leader.
	//   node[j] = leader(erank[j]) exists ? data[leader(erank[j])] : hold[j]
	// Pseudo-random enable-term bit (deterministic in (vidx, term, lane)).
	int en_term_bit(int vidx, int t, int k) const
	{
		uint64_t x = (uint64_t)(vidx * 0x9e3779b1u) ^ ((uint64_t)(t + 1) * 0x85ebca77u) ^
		             ((uint64_t)(k + 1) * 0xc2b2ae3du);
		x ^= x >> 15;
		x *= 0xd6e8feb86659fd93ULL;
		x ^= x >> 31;
		return (int)(x & 1);
	}

	bool fingerprint_gather_compacted(ConstEval &ce, const SigSpec &root,
	                                  const GatherRegion &gr, int64_t cone_est,
	                                  const char *name, bool quick)
	{
		int n = gr.n, nb = gr.nb, slot_w = gr.slot_w, a = gr.slot_w;
		SigSpec en_s = sigmap(gr.en_sig);
		SigSpec sel_s = sigmap(gr.sel_sig);
		SigSpec attr_s = sigmap(gr.attr_sig);
		SigSpec hold_s = sigmap(gr.hold_sig);
		int T = GetSize(gr.en_terms);
		int n_struct = 2 + 3 * n; // structured prefix of make_exclusive_vectors
		vector<vector<int>> lane_vs = make_exclusive_vectors(n);
		vector<vector<int>> sel_vs = make_exclusive_vectors(nb);
		// Quick probe: a small structured subset that rejects wrong
		// (en,sel,direction) combos in a handful of evals before the full sweep.
		int lane_lim = quick ? std::min(6, GetSize(lane_vs)) : GetSize(lane_vs);
		int sel_lim = quick ? std::min(6, GetSize(sel_vs)) : GetSize(sel_vs);
		int vidx = 0;
		for (int li = 0; li < lane_lim; li++) {
			vector<int> &e_struct = lane_vs[li];
			bool rnd = (li >= n_struct); // vary non-primary terms on random tail
			// Realize the lane enable e[] from the composite terms: the first
			// term carries the structured pattern, the rest pass (=1) on
			// structured vectors and are randomized on the tail so each term's
			// AND role is exercised.
			vector<vector<int>> tvals(T, vector<int>(n));
			vector<int> e(n, 1);
			for (int t = 0; t < T; t++) {
				bool neg = gr.en_terms[t].neg;
				for (int k = 0; k < n; k++) {
					int factor = (t == 0) ? e_struct[k] : (rnd ? en_term_bit(li, t, k) : 1);
					tvals[t][k] = neg ? (factor ? 0 : 1) : factor;
					e[k] &= factor;
				}
			}
			ExclResult ar = compute_alloc_exclusive_dir(e, n, nb, gr.msb_first);
			vector<int> leader(nb, -1);
			for (int m = 0; m < nb; m++)
				for (int l = 0; l < n; l++)
					if (ar.done[l] && ar.dsel[l] == m) {
						leader[m] = l;
						break;
					}
			for (int si = 0; si < sel_lim; si++) {
				vector<int> &sv = sel_vs[si];
				vidx++;
				vector<int> data(n), hold(nb);
				for (int l = 0; l < n; l++)
					data[l] = gather_root_payload(vidx, l, a);
				for (int j = 0; j < nb; j++)
					hold[j] = gather_root_payload(vidx, n + j, a);
				vector<int> act(nb);
				for (int j = 0; j < nb; j++) {
					int sj = gr.sel_rev ? (nb - 1 - j) : j;
					act[j] = gr.sel_compl ? (sv[sj] ? 0 : 1) : (sv[sj] ? 1 : 0);
				}
				vector<int> erank = entry_ranks(act, nb, gr.ent_msb_first);
				vector<std::pair<SigSpec, Const>> sets = gr.guard_sets;
				if (T == 0)
					sets.push_back({en_s, pack_lanes(e, 1)});
				else
					for (int t = 0; t < T; t++)
						sets.push_back({sigmap(gr.en_terms[t].bits), pack_lanes(tvals[t], 1)});
				sets.push_back({sel_s, pack_lanes(sv, 1)});
				sets.push_back({attr_s, pack_lanes(data, a)});
				sets.push_back({hold_s, pack_lanes(hold, a)});
				Const res;
				if (!eval_root(ce, sets, root, res, cone_est)) {
					log_debug("  compacted %s: eval failed (vidx %d)\n", name, vidx);
					return false;
				}
				for (int j = 0; j < nb; j++) {
					int m = erank[j];
					bool valid = (m >= 0 && m < nb && leader[m] >= 0);
					int val = (gr.ent_gated && !act[j]) ? hold[j]
					                                    : (valid ? data[leader[m]] : hold[j]);
					for (int b = 0; b < slot_w; b++) {
						bool got = (j * slot_w + b < GetSize(res)) &&
						           res[j * slot_w + b] == State::S1;
						bool exp = (val >> b) & 1;
						if (got != exp) {
							log_debug("  compacted %s: mismatch entry %d bit %d (vidx %d)\n",
							          name, j, b, vidx);
							return false;
						}
					}
				}
			}
		}
		return true;
	}

	// Emit the composed lane-side exclusive scan + identity gather and the
	// entry-side compaction net for a matched compacted region.
	//   slot_data[m]  = data[leader lane of lane-slot m]     (identity gather)
	//   slot_valid[m] = lane-slot m has a leader
	//   erank[j]      = popcount(active[<j])                 (entry prefix)
	//   node[j]       = slot_valid[erank[j]] ? slot_data[erank[j]] : hold[j]
	void emit_gather_compacted(const GatherRegion &gr)
	{
		Region rg;
		rg.n = gr.n;
		rg.nb = gr.nb;
		rg.msb_first = gr.msb_first;
		rg.exclusive = true;
		rg.exclusive_and2 = false;
		rg.field_w = clog2_int(gr.nb + 1);
		rg.anchor = gr.anchor;
		if (rg.anchor == nullptr)
			find_anchor_driver(gr.gather_sig, rg.anchor);
		Cell *anchor = rg.anchor;
		Cell *cell = anchor;  // NEW_ID2_SUFFIX expands to cell->module->uniquify(...)
		int cnt_w = clog2_int(rg.nb + 1);

		// Build the lane enable from the composite terms (or use the single
		// enable bus for the direct path).
		if (gr.en_terms.empty()) {
			rg.en_sig = gr.en_sig;
		} else {
			SigSpec en_bits;
			for (int k = 0; k < gr.n; k++) {
				SigBit e = State::S1;
				for (auto &term : gr.en_terms) {
					SigBit v = sigmap(term.bits)[k];
					if (term.neg)
						v = emit_not(anchor, v);
					e = emit_and(anchor, e, v);
				}
				en_bits.append(e);
			}
			rg.en_sig = en_bits;
		}

		vector<SigBit> leader, grant;
		vector<SigSpec> slot, therm;
		bool use_therm = rg.nb <= max_therm_nb;
		if (use_therm)
			emit_scan_exclusive_therm(rg, leader, therm, grant, slot, cnt_w);
		else
			emit_scan_exclusive_bin(rg, leader, slot, grant, cnt_w);

		XbarCand xb;
		xb.sig = gr.gather_sig;
		xb.name = gr.name;
		xb.nb = gr.nb;
		xb.slot_w = gr.slot_w;
		xb.attr_sig = gr.attr_sig;
		xb.a = gr.slot_w;
		xb.identity = true;
		xb.anchor = anchor;
		SigSpec slot_data = emit_exclusive_gather(rg, xb, grant, slot, cnt_w,
		                                          use_therm ? &therm : nullptr);

		vector<SigBit> slot_valid(rg.nb);
		for (int m = 0; m < rg.nb; m++) {
			SigSpec terms;
			for (int l = 0; l < rg.n; l++) {
				SigBit eqs = use_therm ? emit_therm_eq(anchor, therm[l], m, rg.nb)
				                       : emit_eq_const(anchor, slot[l], m, cnt_w);
				terms.append(emit_and(anchor, grant[l], eqs));
			}
			slot_valid[m] = emit_reduce_or(anchor, terms);
		}

		// Entry-side exclusive thermometer prefix over the active mask.
		SigSpec sel_s = sigmap(gr.sel_sig);
		vector<SigBit> act(rg.nb);
		for (int j = 0; j < rg.nb; j++) {
			int sj = gr.sel_rev ? (rg.nb - 1 - j) : j;
			act[j] = gr.sel_compl ? emit_not(anchor, sel_s[sj]) : SigBit(sel_s[sj]);
		}
		// Entry-side exclusive prefix: thermometer for small nb, else a
		// saturating binary count so wide nb can't emit O(nb^2) prefix logic.
		bool ent_use_therm = rg.nb <= max_therm_nb;
		vector<SigBit> act_p(rg.nb);
		vector<int> ent_of_p(rg.nb);
		for (int p = 0; p < rg.nb; p++) {
			int j = gr.ent_msb_first ? (rg.nb - 1 - p) : p;
			ent_of_p[p] = j;
			act_p[p] = act[j];
		}
		vector<SigSpec> ent_therm(rg.nb), ent_slot(rg.nb);
		if (ent_use_therm) {
			vector<SigSpec> ent_therm_p;
			emit_prefix_therm_log(anchor, act_p, rg.nb, ent_therm_p);
			for (int p = 0; p < rg.nb; p++)
				ent_therm[ent_of_p[p]] = ent_therm_p[p];
		} else {
			vector<SigSpec> ent_slot_p;
			SigSpec ent_total;
			emit_prefix_count_sat_log(anchor, act_p, cnt_w, rg.nb, ent_slot_p, ent_total);
			for (int p = 0; p < rg.nb; p++)
				ent_slot[ent_of_p[p]] = ent_slot_p[p];
		}

		SigSpec hold_s = sigmap(gr.hold_sig);
		SigSpec out;
		for (int j = 0; j < rg.nb; j++) {
			SigSpec cases, sels;
			vector<SigBit> valid_terms;
			for (int m = 0; m < rg.nb; m++) {
				SigBit eqm = ent_use_therm
				             ? emit_therm_eq(anchor, ent_therm[j], m, rg.nb)
				             : emit_eq_const(anchor, ent_slot[j], m, cnt_w);
				sels.append(eqm);
				cases.append(slot_data.extract(m * gr.slot_w, gr.slot_w));
				valid_terms.push_back(emit_and(anchor, eqm, slot_valid[m]));
			}
			Wire *dy = module->addWire(NEW_ID2_SUFFIX("ffa_compact_gather"), gr.slot_w);
			module->addPmux(NEW_ID2_SUFFIX("ffa_compact_gather_pmux"),
			                Const(0, gr.slot_w), cases, sels, dy, cell_src(anchor));
			cells_added++;
			SigBit valid_j = emit_reduce_or(anchor, SigSpec(valid_terms));
			if (gr.ent_gated)
				valid_j = emit_and(anchor, valid_j, act[j]);
			SigSpec hold_j = hold_s.extract(j * gr.slot_w, gr.slot_w);
			out.append(emit_mux(anchor, hold_j, SigSpec(dy), valid_j));
		}
		int dn = connect_driven(gr.gather_sig, out, anchor, "ffa_gather_dangling");
		claim_region(gr.gather_sig, gr.cut_cells);
		regions_rewritten++;
		std::string en_desc;
		if (gr.en_terms.empty()) {
			en_desc = log_signal(gr.en_sig);
		} else {
			for (auto &t : gr.en_terms) {
				if (!en_desc.empty())
					en_desc += "&";
				en_desc += std::string(t.neg ? "!" : "") + t.name;
			}
		}
		log("  %s: %s <- first_fit_alloc gather-rooted-compacted(en=%s, sel=%s%s, "
		    "nb=%d, slot_w=%d, lane=%s ent=%s) [%d bit(s) re-driven]\n",
		    log_id(module), gr.name.c_str(), en_desc.c_str(),
		    gr.sel_compl ? "!" : "", log_signal(gr.sel_sig), gr.nb, gr.slot_w,
		    gr.msb_first ? "MSB" : "LSB", gr.ent_msb_first ? "MSB" : "LSB", dn);
	}

	// A per-lane source recovered from cut leaves. `bits` is lane-major (lane
	// k occupies [k*w, (k+1)*w)), gathered through the source's affine
	// index/bit stride so lanes 0..n-1 line up on strided array elements.
	struct LaneSrc {
		std::string id;
		int w = 0;
		SigSpec bits;
	};

	// Group cut leaves by source stem into idx -> (offset -> bit). A wire
	// "base[idx]" (Verific's per-element array lowering) contributes idx; a
	// plain bus contributes idx -1. Offsets are the bit positions within the
	// element/bus.
	std::map<std::string, std::map<int, std::map<int, SigBit>>>
	group_leaf_srcs(const pool<SigBit> &leaves)
	{
		std::map<std::string, std::map<int, std::map<int, SigBit>>> g;
		for (auto bit : leaves) {
			if (!bit.wire)
				continue;
			std::string base;
			int idx = -1;
			if (parse_indexed_port_name(bit.wire, base, idx))
				g[base][idx][(int)bit.offset] = bit;
			else
				g[bit.wire->name.str()][-1][(int)bit.offset] = bit;
		}
		return g;
	}

	// Candidate lane counts implied by the cut leaves. A source spread over
	// several array indices offers #idx lanes (array-of-lanes); a single
	// packed element offers #offset lanes (and bit-per-lane divisors).
	std::set<int> lane_count_candidates(const pool<SigBit> &leaves)
	{
		auto g = group_leaf_srcs(leaves);
		std::set<int> ns;
		for (auto &kv : g) {
			int ni = GetSize(kv.second);
			if (ni > 1) {
				ns.insert(ni);
			} else {
				int no = GetSize(kv.second.begin()->second);
				ns.insert(no);
				for (int w = 2; w <= max_gather_w; w++)
					if (no % w == 0)
						ns.insert(no / w);
			}
		}
		return ns;
	}

	// Partition `leaves` into per-source lane groups for n lanes. Each source
	// is either an array-of-lanes (n strided array indices, w bits each) or a
	// single packed element whose bit offsets carry the lanes (contiguous, or
	// bit-strided when 1 bit/lane). Every source must map exactly onto lanes
	// 0..n-1 in lane-major order.
	bool partition_lane_srcs(const pool<SigBit> &leaves, int n, vector<LaneSrc> &out)
	{
		auto g = group_leaf_srcs(leaves);
		if (g.empty() || GetSize(g) != count_leaf_srcs(leaves))
			return false; // an unnamed leaf slipped through
		for (auto &kv : g) {
			LaneSrc ls;
			ls.id = kv.first;
			auto &byidx = kv.second;
			vector<int> idxv;
			for (auto &p : byidx)
				idxv.push_back(p.first);
			if (GetSize(idxv) == n) {
				// array-of-lanes: array index is the lane axis
				std::sort(idxv.begin(), idxv.end());
				int stride = (n > 1) ? (idxv[1] - idxv[0]) : 1;
				if (stride <= 0)
					return false;
				vector<int> ov;
				for (auto &p : byidx[idxv[0]])
					ov.push_back(p.first);
				std::sort(ov.begin(), ov.end());
				int w = GetSize(ov);
				ls.w = w;
				for (int k = 0; k < n; k++) {
					if (idxv[k] != idxv[0] + k * stride)
						return false;
					auto &m = byidx[idxv[k]];
					if (GetSize(m) != w)
						return false;
					for (int o = 0; o < w; o++) {
						auto it = m.find(ov[o]);
						if (it == m.end())
							return false;
						ls.bits.append(it->second);
					}
				}
			} else if (GetSize(idxv) == 1) {
				// single packed element: bit offset is the lane/bit axis
				auto &m = byidx[idxv[0]];
				vector<int> ov;
				for (auto &p : m)
					ov.push_back(p.first);
				std::sort(ov.begin(), ov.end());
				int total = GetSize(ov);
				if (total % n != 0)
					return false;
				int w = total / n;
				ls.w = w;
				if (w == 1) {
					int stride = (n > 1) ? (ov[1] - ov[0]) : 1;
					if (stride <= 0)
						return false;
					for (int k = 0; k < n; k++) {
						if (ov[k] != ov[0] + k * stride)
							return false;
						ls.bits.append(m[ov[k]]);
					}
				} else {
					for (int i = 0; i < n * w; i++)
						ls.bits.append(m[ov[i]]); // contiguous lane-major
				}
			} else {
				return false;
			}
			out.push_back(ls);
		}
		return true;
	}

	int count_leaf_srcs(const pool<SigBit> &leaves)
	{
		std::set<std::string> srcs;
		for (auto bit : leaves) {
			if (!bit.wire)
				return -1;
			std::string base;
			int idx = -1;
			srcs.insert(parse_indexed_port_name(bit.wire, base, idx) ? base
			                                                          : bit.wire->name.str());
		}
		return GetSize(srcs);
	}

	// Split reconstructed lane sources into the data payload (one wide source
	// of width slot_w) and the 1-bit enable factors. The enable list may be
	// empty here when a materialized internal enable bus supplies the enable;
	// the caller checks the combined term count.
	bool classify_srcs(const vector<LaneSrc> &srcs, int n, int slot_w,
	                   SigSpec &attr_sig, vector<EnTerm> &en_terms)
	{
		vector<const LaneSrc *> wide, thin;
		for (auto &s : srcs) {
			if (slot_w > 1 && s.w == slot_w)
				wide.push_back(&s);
			else if (s.w == 1)
				thin.push_back(&s);
			else
				return false; // unexpected width -> not this shape
		}
		if (slot_w > 1) {
			if (GetSize(wide) != 1)
				return false;
			attr_sig = wide[0]->bits;
		} else {
			// slot_w == 1: no separate wide payload; the gather value is the
			// done bit (all-ones data). Use a constant payload.
			attr_sig = SigSpec(State::S1, n);
		}
		for (auto s : thin)
			en_terms.push_back({s->bits, false, s->id});
		return true;
	}

	// Try to match an entry-side-compacted gather rooted at `root_in`: the nb
	// slots are read by an entry-side compaction (entry j draws lane-slot
	// popcount(active[<j])) rather than by direct index. `hold_in` is the
	// per-slot FF-Q hold value used when no lane is granted. The lane enable
	// and (strided) data payload are reconstructed from the cut leaves.
	bool match_gather_compacted(const SigSpec &root_in, int slots, int slot_w,
	                            const std::string &name, const SigSpec &hold_in,
	                            GatherRegion &out)
	{
		if (GetSize(hold_in) != slots * slot_w)
			return false;
		SigSpec root = sigmap(root_in);
		SigSpec hold = sigmap(hold_in);
		if (!sig_bus_ok(hold))
			return false;
		pool<Cell *> cone_cells;
		pool<SigBit> leaf_bits;
		int max_cone = std::max(512, max_n * 256);
		int max_leaf = max_n * max_n + max_n * 64 + max_n;
		if (!get_cone(root, cone_cells, leaf_bits, max_cone, max_leaf))
			return false;
		if (cone_cells.empty())
			return false;
		bool has_mux = false;
		for (auto c : cone_cells)
			if (c->type.in(ID($mux), ID($pmux), ID($bmux))) {
				has_mux = true;
				break;
			}
		if (!has_mux)
			return false;
		// The hold value must be a cone leaf (the register Q feedback), not a
		// signal recomputed inside the allocation cone.
		pool<SigBit> hold_bits = sig_bit_pool(hold);
		for (auto bit : hold_bits) {
			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv != nullptr && cone_cells.count(drv))
				return false;
		}

		vector<BusCand> sel_cands =
		    collect_gather_en_cands(cone_cells, slots, slots, max_sel_cands);
		if (dbg_compact)
			log("    [dbg] try compacted %s (slots=%d, slot_w=%d): cone %d cells, %d sel\n",
			    name.c_str(), slots, slot_w, GetSize(cone_cells), GetSize(sel_cands));
		log_debug("ffa: compacted %s (slots=%d, slot_w=%d): cone %d cells, %d sel\n",
		          name.c_str(), slots, slot_w, GetSize(cone_cells), GetSize(sel_cands));
		ConstEval ce(module);
		int64_t cone_est = GetSize(cone_cells) + 16;
		// Leaves left after removing sel+hold(+en-bus) hold the remaining lane
		// enable factors and the (possibly strided) data payload; bound how
		// many we reconstruct.
		int extra_cap = max_n * (max_gather_w + 4) + 64;

		for (auto &sel : sel_cands) {
			if (walk_exhausted() || eval_exhausted())
				break;
			pool<SigBit> sel_bits = sig_bit_pool(sel.sig);
			bool overlap = false;
			for (auto b : sel_bits)
				if (hold_bits.count(b)) {
					overlap = true;
					break;
				}
			if (overlap)
				continue;
			pool<SigBit> base0 = sel_bits;
			for (auto b : hold_bits)
				base0.insert(b);
			pool<SigBit> extra0;
			if (!cut_cone_extra_leaves(root, base0, GetSize(cone_cells) + 32, extra0,
			                           extra_cap)) {
				if (dbg_compact)
					log("    [dbg] sel=%s: cut_extra failed\n", sel.name.c_str());
				continue;
			}
			if (extra0.empty())
				continue;
			// Lane count comes from the strided data / primary enable leaves
			// left after removing sel+hold (a derived enable bus is cut below).
			std::set<int> n_cands = lane_count_candidates(extra0);
			for (int n : n_cands) {
				if (n < min_n || n > max_n || slots > n)
					continue;
				// Emit-size guard: the compacted net is ~n*nb*slot_w (lane scan +
				// identity gather) plus nb*nb*slot_w (entry pmux). Skip candidates
				// whose emit would explode compile/techmap cost.
				int64_t emit_bits =
				    (int64_t)(n + slots) * slots * slot_w;
				if (emit_bits > max_xbar_emit_bits)
					continue;
				if (walk_exhausted() || eval_exhausted())
					break;
				// A derived enable factor (e.g. `!lhit`) is not a cut leaf;
				// pin one width-n internal bus as a boundary so it acts as a
				// forceable per-lane enable term. ei == -1 covers designs whose
				// enable factors are all primary/strided leaves.
				vector<BusCand> eb_cands =
				    collect_internal_buses(cone_cells, n, max_gather_en);
				if (dbg_compact) {
					std::string s;
					for (auto &e : eb_cands)
						s += " " + e.name;
					log("    [dbg] sel=%s n=%d: %d internal en-bus(es):%s\n", sel.name.c_str(),
					    n, GetSize(eb_cands), s.c_str());
				}
				for (int ei = -1; ei < GetSize(eb_cands); ei++) {
					if (eval_exhausted())
						break;
					const BusCand *eb = (ei >= 0) ? &eb_cands[ei] : nullptr;
					pool<SigBit> base = base0;
					SigSpec eb_sig;
					if (eb != nullptr) {
						eb_sig = sigmap(eb->sig);
						pool<SigBit> ebb = sig_bit_pool(eb_sig);
						bool clash = false;
						for (auto b : ebb)
							if (base.count(b)) {
								clash = true;
								break;
							}
						if (clash)
							continue;
						for (auto b : ebb)
							base.insert(b);
					}
					pool<SigBit> extra;
					if (eb == nullptr)
						extra = extra0;
					else if (!cut_cone_extra_leaves(root, base, GetSize(cone_cells) + 32, extra,
					                                extra_cap))
						continue;
					if (extra.empty())
						continue;
					vector<LaneSrc> srcs;
					if (!partition_lane_srcs(extra, n, srcs)) {
						if (dbg_compact && eb == nullptr) {
							std::string s;
							auto g = group_leaf_srcs(extra);
							for (auto &kv : g) {
								int no = GetSize(kv.second.begin()->second);
								s += stringf(" %s[#idx=%d,off=%d]", kv.first.c_str(),
								             GetSize(kv.second), no);
							}
							log("    [dbg] sel=%s n=%d: partition failed (%d extra):%s\n",
							    sel.name.c_str(), n, GetSize(extra), s.c_str());
						}
						continue;
					}
					SigSpec attr_sig;
					vector<EnTerm> en_terms;
					if (!classify_srcs(srcs, n, slot_w, attr_sig, en_terms))
						continue;
					// A cut-leaf enable bus (eb) may be flattened in the opposite
					// lane order from the array-index-ordered strided leaves; try
					// both so per-lane alignment can be recovered.
					SigSpec eb_rev_sig;
					if (eb != nullptr) {
						for (int k = n - 1; k >= 0; k--)
							eb_rev_sig.append(eb_sig[k]);
						en_terms.insert(en_terms.begin(), {eb_sig, false, eb->name});
					}
					int T = GetSize(en_terms);
					if (T < 1 || T > 4)
						continue;
					if (dbg_compact)
						log("    [dbg] %s: sel=%s n=%d eb=%s: partition ok, %d src, T=%d, "
						    "slot_w=%d\n",
						    name.c_str(), sel.name.c_str(), n, eb ? eb->name.c_str() : "-",
						    GetSize(srcs), T, slot_w);
					pool<SigBit> allowed = base;
					for (auto &s : srcs)
						for (auto b : sig_bit_pool(s.bits))
							allowed.insert(b);
					pool<SigBit> hit;
					pool<Cell *> cut_cells;
					if (!cut_cone_walk(root, allowed, GetSize(cone_cells) + 32, &hit, &cut_cells,
					                   &allowed, &leaf_bits, &cone_cells))
						continue;
					bool conflict = false;
					for (auto b : allowed) {
						Cell *drv = bit_to_driver.at(b, nullptr);
						if (drv != nullptr && cut_cells.count(drv)) {
							conflict = true;
							break;
						}
					}
					if (conflict)
						continue;

					int ebr_lim = (eb != nullptr) ? 2 : 1;
					for (int ebr = 0; ebr < ebr_lim; ebr++)
						for (int pol = 0; pol < (1 << T); pol++)
							for (int lane_dir = 0; lane_dir < 2; lane_dir++)
								for (int ent_dir = 0; ent_dir < 2; ent_dir++)
									for (int cpl = 0; cpl < 2; cpl++)
										for (int srev = 0; srev < 2; srev++)
											for (int eg = 0; eg < 2; eg++) {
												if (eval_exhausted())
													break;
												GatherRegion gr;
												gr.n = n;
												gr.nb = slots;
												gr.msb_first = (lane_dir == 1);
												gr.attr_sig = attr_sig;
												gr.slot_w = slot_w;
												gr.sel_sig = sel.sig;
												gr.sel_compl = (cpl == 1);
												gr.sel_rev = (srev == 1);
												gr.ent_msb_first = (ent_dir == 1);
												gr.hold_sig = hold;
												gr.compacted = true;
												gr.ent_gated = (eg == 1);
												gr.en_terms = en_terms;
												if (eb != nullptr)
													gr.en_terms[0].bits = (ebr == 1) ? eb_rev_sig : eb_sig;
												for (int t = 0; t < T; t++)
													gr.en_terms[t].neg = (pol >> t) & 1;
												if (!fingerprint_gather_compacted(ce, root, gr, cone_est,
												                                  name.c_str(), true))
													continue;
												if (!fingerprint_gather_compacted(ce, root, gr, cone_est,
												                                  name.c_str(), false))
													continue;
												gr.gather_sig = root;
												gr.name = name;
												gr.cut_cells = cut_cells;
												find_anchor_driver(root, gr.anchor);
												out = gr;
												log_debug("  compacted %s: MATCH n=%d nb=%d lane=%s "
												          "ent=%s sel=%s%s%s eb=%s%s terms=%d gated=%d\n",
												          name.c_str(), n, slots,
												          gr.msb_first ? "MSB" : "LSB",
												          gr.ent_msb_first ? "MSB" : "LSB",
												          gr.sel_compl ? "!" : "",
												          gr.sel_rev ? "rev " : "", sel.name.c_str(),
												          eb ? eb->name.c_str() : "-",
												          (eb && ebr == 1) ? "(rev)" : "", T,
												          gr.ent_gated);
												return true;
											}
				}
			}
		}
		return false;
	}

	// Candidate gather roots: per-slot flop-D packs grouped by register stem,
	// plus split-array buses of equal-width elements. Unlike
	// collect_exclusive_gather_cands this is not gated on a known nb: the
	// slot count comes from the candidate itself.
	vector<GatherCand> collect_gather_roots()
	{
		// Map each FF D bit to its aligned Q bit, so a gather root that feeds a
		// register (directly or as a split-array slice) can recover the per-slot
		// hold value the allocation branch keeps when no lane is granted.
		dict<SigBit, SigBit> ffd_to_q;
		for (auto c : module->cells()) {
			if (!is_gather_ff(c) || !c->hasPort(ID::D) || !c->hasPort(ID::Q))
				continue;
			SigSpec d = c->getPort(ID::D), q = c->getPort(ID::Q);
			int w = std::min(GetSize(d), GetSize(q));
			for (int i = 0; i < w; i++)
				ffd_to_q[sigmap(d[i])] = sigmap(q[i]);
		}
		auto derive_hold = [&](const SigSpec &sig) -> SigSpec {
			SigSpec s = sigmap(sig);
			SigSpec hold;
			for (auto bit : s) {
				auto it = ffd_to_q.find(bit);
				if (it == ffd_to_q.end())
					return SigSpec();
				hold.append(it->second);
			}
			return hold;
		};

		vector<GatherCand> cands;
		pool<SigSpec> seen;
		auto add = [&](const SigSpec &sig, const std::string &nm, int slots, int slot_w,
		               SigSpec hold = SigSpec()) {
			if (slots < min_slots || slots > max_n)
				return;
			if (slot_w < 1 || slot_w > max_gather_w)
				return;
			SigSpec s = sigmap(sig);
			if (!sig_bus_ok(s) || root_claimed(s))
				return;
			if (!seen.insert(s).second)
				return;
			if (hold.empty())
				hold = derive_hold(sig);
			GatherCand gc;
			gc.sig = sig;
			gc.name = nm;
			gc.slots = slots;
			gc.slot_w = slot_w;
			gc.hold_sig = hold;
			cands.push_back(gc);
		};

		std::map<std::string, vector<std::pair<int, Cell *>>> ff_groups;
		for (auto c : module->cells()) {
			if (!is_gather_ff(c) || !c->hasPort(ID::Q) || !c->hasPort(ID::D))
				continue;
			SigSpec q = c->getPort(ID::Q);
			if (q.empty() || !q[0].wire)
				continue;
			std::string base;
			int idx = -1;
			if (parse_indexed_port_name(q[0].wire, base, idx))
				ff_groups[base].push_back({idx, c});
		}
		for (auto &kv : ff_groups) {
			auto entries = kv.second;
			std::sort(entries.begin(), entries.end(),
			          [](const std::pair<int, Cell *> &a, const std::pair<int, Cell *> &b) {
			              return a.first < b.first;
			          });
			int slot_w = GetSize(entries.front().second->getPort(ID::D));
			bool ok = slot_w >= 1;
			for (auto &e : entries)
				if (GetSize(e.second->getPort(ID::D)) != slot_w) {
					ok = false;
					break;
				}
			if (!ok)
				continue;
			// Contiguous index run only (compaction indexes slots by position).
			bool contiguous = true;
			for (int i = 0; i < GetSize(entries); i++)
				if (entries[i].first != entries.front().first + i) {
					contiguous = false;
					break;
				}
			if (!contiguous)
				continue;
			SigSpec pack, qpack;
			for (auto &e : entries) {
				pack.append(e.second->getPort(ID::D));
				qpack.append(e.second->getPort(ID::Q));
			}
			// The per-slot FF-Q is the hold value the allocation branch keeps
			// when no lane is granted (needed to model entry-side compaction).
			add(pack, stringf("gather_ff[%s]", kv.first.c_str()), GetSize(entries),
			    slot_w, qpack);
		}

		vector<Wire *> all;
		for (auto w : module->wires())
			all.push_back(w);
		for (auto &bus : collect_split_buses(all)) {
			if (bus.entries < min_slots || bus.entries > max_n)
				continue;
			if (bus.elem_width < 1 || bus.elem_width > max_gather_w)
				continue;
			add(bus.sig, bus.name, bus.entries, bus.elem_width);
		}

		if (GetSize(cands) > max_gather_roots)
			cands.resize(max_gather_roots);
		return cands;
	}

	// Collect width-w 1-bit-lane buses from a gather cone, for w in [lo, hi].
	// Shallow (leaf-side) buses first, then capped. Used both for the lane
	// enable bus (w in [min_n, max_n]) and the entry-select bus (w == nb).
	vector<BusCand> collect_gather_en_cands(const pool<Cell *> &cone_cells, int lo,
	                                        int hi, int cap)
	{
		pool<SigBit> internal_bits;
		for (auto c : cone_cells)
			for (auto &conn : c->connections())
				if (c->output(conn.first))
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							internal_bits.insert(bit);
		auto all_internal_or_input = [&](const SigSpec &s) {
			for (auto bit : s)
				if (!bit.wire || (!internal_bits.count(bit) &&
				                  bit_to_driver.at(bit, nullptr) != nullptr))
					return false;
			return true;
		};
		vector<BusCand> cands;
		pool<SigSpec> seen;
		auto add = [&](const SigSpec &sig, const std::string &nm) {
			SigSpec s = sigmap(sig);
			int w = GetSize(s);
			if (w < lo || w > hi)
				return;
			if (!sig_bus_ok(s) || !all_internal_or_input(s))
				return;
			if (!seen.insert(s).second)
				return;
			cands.push_back({s, nm, w, 1});
		};
		for (auto w : module->wires())
			add(SigSpec(w), w->name.str());
		for (auto &bus : collect_cone_split_buses(internal_bits))
			if (bus.elem_width == 1)
				add(bus.sig, bus.name);

		dict<Cell *, int> depth = compute_cone_depths(cone_cells);
		auto bus_depth = [&](const SigSpec &s) {
			int d = 0;
			for (auto bit : s) {
				Cell *drv = bit_to_driver.at(bit, nullptr);
				if (drv != nullptr)
					d = std::max(d, depth.at(drv, 1 << 30));
			}
			return d;
		};
		std::stable_sort(cands.begin(), cands.end(),
		                 [&](const BusCand &a, const BusCand &b) {
		                     return bus_depth(a.sig) < bus_depth(b.sig);
		                 });
		if (GetSize(cands) > cap)
			cands.resize(cap);
		return cands;
	}
	vector<BusCand> collect_gather_en_cands(const pool<Cell *> &cone_cells)
	{
		return collect_gather_en_cands(cone_cells, min_n, max_n, max_gather_en);
	}

	// Width-w buses driven entirely inside the cone (combinational, not FF-Q
	// or primary input). These are the derived enable factors (e.g. `lhit`)
	// that the composite-enable matcher pins as a forceable cut boundary;
	// FF-Q/primary enables are handled as leaves via the extra-leaf partition.
	// Sorted deepest-first, since a derived enable sits above the raw inputs.
	vector<BusCand> collect_internal_buses(const pool<Cell *> &cone_cells, int w, int cap)
	{
		pool<SigBit> internal_bits;
		for (auto c : cone_cells)
			for (auto &conn : c->connections())
				if (c->output(conn.first))
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							internal_bits.insert(bit);
		auto all_internal = [&](const SigSpec &s) {
			for (auto bit : s)
				if (!bit.wire || !internal_bits.count(bit))
					return false;
			return true;
		};
		vector<BusCand> cands;
		pool<SigSpec> seen;
		auto add = [&](const SigSpec &sig, const std::string &nm) {
			SigSpec s = sigmap(sig);
			if (GetSize(s) != w || !sig_bus_ok(s) || !all_internal(s))
				return;
			if (!seen.insert(s).second)
				return;
			cands.push_back({s, nm, w, 1});
		};
		for (auto wr : module->wires())
			add(SigSpec(wr), wr->name.str());
		for (auto &bus : collect_cone_split_buses(internal_bits))
			if (bus.elem_width == 1)
				add(bus.sig, bus.name);
		dict<Cell *, int> depth = compute_cone_depths(cone_cells);
		auto bus_depth = [&](const SigSpec &s) {
			int d = 0;
			for (auto bit : s) {
				Cell *drv = bit_to_driver.at(bit, nullptr);
				if (drv != nullptr)
					d = std::max(d, depth.at(drv, 1 << 30));
			}
			return d;
		};
		std::stable_sort(cands.begin(), cands.end(),
		                 [&](const BusCand &a, const BusCand &b) {
		                     return bus_depth(a.sig) > bus_depth(b.sig);
		                 });
		if (GetSize(cands) > cap)
			cands.resize(cap);
		return cands;
	}

	// Try to match a direct-index exclusive identity gather rooted at the
	// slot-major bus `root_in` (slot s read by index s; no guards). Fills
	// `out`. `slots`/`slot_w` describe the bus layout; `name` is for logs.
	bool match_gather_core(const SigSpec &root_in, int slots, int slot_w,
	                       const std::string &name, GatherRegion &out)
	{
		SigSpec root = sigmap(root_in);
		pool<Cell *> cone_cells;
		pool<SigBit> leaf_bits;
		int max_cone = std::max(512, max_n * 256);
		int max_leaf = max_n * max_n + max_n * 64 + max_n;
		if (!get_cone(root, cone_cells, leaf_bits, max_cone, max_leaf))
			return false;
		if (cone_cells.empty())
			return false;

		// Cheap structural pre-filter: a gather is a mux/priority network.
		bool has_mux = false;
		for (auto c : cone_cells)
			if (c->type.in(ID($mux), ID($pmux), ID($bmux))) {
				has_mux = true;
				break;
			}
		if (!has_mux)
			return false;

		vector<BusCand> en_cands = collect_gather_en_cands(cone_cells);
		log_debug("ffa: gather-root %s (slots=%d, slot_w=%d): cone %d cells, %d en cand(s)\n",
		          name.c_str(), slots, slot_w, GetSize(cone_cells), GetSize(en_cands));
		ConstEval ce(module);
		int64_t cone_est = GetSize(cone_cells) + 16;

		for (auto &en : en_cands) {
			if (walk_exhausted() || eval_exhausted())
				break;
			int n = GetSize(en.sig);
			if (slots > n)
				continue;
			pool<SigBit> en_bits = sig_bit_pool(en.sig);
			pool<SigBit> extra;
			if (!cut_cone_extra_leaves(root, en_bits, GetSize(cone_cells) + 32, extra,
			                           n * slot_w + 8))
				continue;
			SigSpec attr_sig;
			int a = 0;
			vector<FieldKey> attr_keys;
			if (!group_lane_field(extra, n, attr_sig, a, &attr_keys))
				continue;
			if (a != slot_w)
				continue;
			pool<SigBit> allowed = en_bits;
			for (auto bit : sig_bit_pool(attr_sig))
				allowed.insert(bit);
			pool<SigBit> hit;
			pool<Cell *> cut_cells;
			if (!cut_cone_walk(root, allowed, GetSize(cone_cells) + 32, &hit, &cut_cells,
			                   &allowed, &leaf_bits, &cone_cells))
				continue;
			bool conflict = false;
			for (auto bit : allowed) {
				Cell *drv = bit_to_driver.at(bit, nullptr);
				if (drv != nullptr && cut_cells.count(drv)) {
					conflict = true;
					break;
				}
			}
			if (conflict)
				continue;

			for (int dir = 0; dir < 2; dir++) {
				if (eval_exhausted())
					break;
				GatherRegion gr;
				gr.en_sig = en.sig;
				gr.n = n;
				gr.nb = slots;
				gr.msb_first = (dir == 1);
				gr.attr_sig = attr_sig;
				gr.slot_w = slot_w;
				gr.attr_keys = attr_keys;
				if (!fingerprint_gather_rooted(ce, root, gr, cone_est, name.c_str()))
					continue;
				gr.gather_sig = root;
				gr.name = name;
				gr.cut_cells = cut_cells;
				find_anchor_driver(root, gr.anchor);
				out = gr;
				log_debug("  gather-root %s: MATCH n=%d nb=%d %s slot_w=%d en=%s\n",
				          name.c_str(), n, gr.nb, gr.msb_first ? "MSB" : "LSB",
				          slot_w, en.name.c_str());
				return true;
			}
		}
		return false;
	}

	// ---- guard-mux peeling ----
	// A gather is often buried under guard muxes (an FSM `case`, a per-slot
	// `hit` mux) that select between the allocation branch and a hold/update
	// branch. We descend into the mux inputs (a bounded DFS) and re-attempt
	// the clean match on each inner sub-node; the guards stay intact and only
	// the isolated allocation branch is re-driven.
	int max_peel_attempts = 64;

	int mux_num_sides(Cell *mux)
	{
		if (mux->type == ID($mux))
			return 2;
		if (mux->type == ID($bmux))
			return 1 << GetSize(mux->getPort(ID::S)); // 2^S_WIDTH case entries
		return 1 + GetSize(mux->getPort(ID::S)); // $pmux: default + cases
	}

	SigBit mux_side_bit(Cell *mux, int ypos, int side)
	{
		SigSpec a = mux->getPort(ID::A);
		if (mux->type == ID($mux))
			return side == 0 ? a[ypos] : mux->getPort(ID::B)[ypos];
		if (mux->type == ID($bmux)) {
			int ow = GetSize(mux->getPort(ID::Y));
			return a[side * ow + ypos]; // A holds 2^S_WIDTH aligned case slices
		}
		if (side == 0)
			return a[ypos]; // $pmux default branch
		int ow = GetSize(a);
		return mux->getPort(ID::B)[(side - 1) * ow + ypos];
	}

	// Build the candidate child buses one guard level below `node_bus`. The
	// lowered netlist bit-blasts guards, so each output bit is driven by its
	// own 1-bit $mux/$pmux (possibly with a per-slot select, e.g. hit[j]). For
	// each descent side we collect that side's aligned input bit of every
	// output bit's driver, preserving slot-major bit order. All bits must use
	// muxes of the same arity, else the guard level is not uniform.
	bool peel_children(const SigSpec &node_bus, vector<SigSpec> &children)
	{
		int nbits = GetSize(node_bus);
		if (nbits < 1)
			return false;
		vector<Cell *> drv(nbits);
		vector<int> yofs(nbits);
		int nsides = -1;
		for (int i = 0; i < nbits; i++) {
			SigBit sb = sigmap(node_bus[i]);
			Cell *c = bit_to_driver.at(sb, nullptr);
			if (c == nullptr || !c->type.in(ID($mux), ID($pmux), ID($bmux)))
				return false;
			SigSpec y = sigmap(c->getPort(ID::Y));
			int pos = -1;
			for (int q = 0; q < GetSize(y); q++)
				if (y[q] == sb) {
					pos = q;
					break;
				}
			if (pos < 0)
				return false;
			int ns = mux_num_sides(c);
			if (ns > 9)
				return false; // over-wide $pmux: too many descent options
			if (nsides < 0)
				nsides = ns;
			else if (nsides != ns)
				return false;
			drv[i] = c;
			yofs[i] = pos;
		}
		if (nsides < 2)
			return false;
		for (int side = 0; side < nsides; side++) {
			SigSpec child;
			for (int i = 0; i < nbits; i++)
				child.append(mux_side_bit(drv[i], yofs[i], side));
			children.push_back(child);
		}
		return true;
	}

	// Peel guard muxes (bounded DFS) and match the clean gather at each inner
	// node. The first matching sub-node wins; guards above it are untouched.
	bool match_gather_peeled(const GatherCand &cand, GatherRegion &out)
	{
		vector<std::pair<SigSpec, int>> stack;
		stack.push_back({sigmap(cand.sig), 0});
		pool<SigSpec> visited;
		int attempts = 0;
		while (!stack.empty()) {
			if (walk_exhausted() || eval_exhausted())
				break;
			auto nd = stack.back();
			stack.pop_back();
			SigSpec bus = nd.first;
			int depth = nd.second;
			if (!visited.insert(bus).second)
				continue;
			if (root_claimed(bus))
				continue;
			if (attempts++ >= max_peel_attempts)
				break;
			std::string nm = depth == 0 ? cand.name
			                            : stringf("%s/peel%d", cand.name.c_str(), depth);
			if (match_gather_core(bus, cand.slots, cand.slot_w, nm, out))
				return true;
			// Entry-side-compacted gather (needs a per-slot FF-Q hold value).
			if (GetSize(cand.hold_sig) == cand.slots * cand.slot_w &&
			    match_gather_compacted(bus, cand.slots, cand.slot_w, nm, cand.hold_sig, out))
				return true;
			if (depth >= max_guard_peel)
				continue;
			vector<SigSpec> children;
			if (!peel_children(bus, children))
				continue;
			log_debug("  peel %s depth %d: %d child branch(es)\n",
			          cand.name.c_str(), depth, GetSize(children));
			for (auto &ch : children)
				if (sig_bus_ok(ch))
					stack.push_back({sigmap(ch), depth + 1});
		}
		return false;
	}

	// Emit the log-depth exclusive scan + identity gather for a matched
	// gather-rooted region and re-drive the gather output.
	void emit_gather_region(const GatherRegion &gr)
	{
		Region rg;
		rg.n = gr.n;
		rg.nb = gr.nb;
		rg.msb_first = gr.msb_first;
		rg.exclusive = true;
		rg.exclusive_and2 = false;
		rg.en_sig = gr.en_sig;
		rg.field_w = clog2_int(gr.nb + 1);
		rg.anchor = gr.anchor;
		if (rg.anchor == nullptr)
			find_anchor_driver(gr.gather_sig, rg.anchor);

		int cnt_w = clog2_int(rg.nb + 1);
		vector<SigBit> leader, grant;
		vector<SigSpec> slot, therm;
		bool use_therm = rg.nb <= max_therm_nb;
		if (use_therm)
			emit_scan_exclusive_therm(rg, leader, therm, grant, slot, cnt_w);
		else
			emit_scan_exclusive_bin(rg, leader, slot, grant, cnt_w);

		XbarCand xb;
		xb.sig = gr.gather_sig;
		xb.name = gr.name;
		xb.nb = gr.nb;
		xb.slot_w = gr.slot_w;
		xb.attr_sig = gr.attr_sig;
		xb.a = gr.slot_w;
		xb.identity = true;
		xb.anchor = rg.anchor;

		SigSpec new_g = emit_exclusive_gather(rg, xb, grant, slot, cnt_w,
		                                      use_therm ? &therm : nullptr);
		int dn = connect_driven(gr.gather_sig, new_g, rg.anchor, "ffa_gather_dangling");
		claim_region(gr.gather_sig, gr.cut_cells);
		regions_rewritten++;
		log("  %s: %s <- first_fit_alloc gather-rooted(en=%s, nb=%d, slot_w=%d, %s) "
		    "[%d bit(s) re-driven]\n",
		    log_id(module), gr.name.c_str(), log_signal(gr.en_sig), gr.nb, gr.slot_w,
		    gr.msb_first ? "MSB-first" : "LSB-first", dn);
	}

	void run_gather_rooted()
	{
		if (!gather_root || module->has_processes_warn())
			return;
		vector<GatherCand> roots = collect_gather_roots();
		log_debug("ffa: %d gather-root candidate(s) in %s\n", GetSize(roots), log_id(module));
		for (auto &cand : roots) {
			if (walk_exhausted() || eval_exhausted())
				break;
			if (root_claimed(cand.sig))
				continue;
			GatherRegion gr;
			if (match_gather_peeled(cand, gr)) {
				if (gr.compacted)
					emit_gather_compacted(gr);
				else
					emit_gather_region(gr);
				continue;
			}
		}
	}

	void run()
	{
		if (module->has_processes_warn())
			return;

		vector<RootSplit> roots = collect_split_roots();
		log_debug("ffa: %d split-root candidate(s) in %s\n", GetSize(roots), log_id(module));
		for (auto &r : roots)
			log_debug("  cand root %s (n=%d, elem=%d)\n", r.name.c_str(), r.n, r.elem);

		for (auto &root : roots) {
			if (walk_exhausted() || eval_exhausted())
				break;
			if (root_claimed(root.sig))
				continue;

			Region rg;
			if (!match_dsel(root.sig, root.name, root.n, root.elem, rg))
				continue;

			// === Exclusive saturating first-fit ===
			if (rg.exclusive) {
				log_assert(rg.exclusive && rg.nb >= 1);

				// Match the grant/done bus and the identity gather BEFORE
				// emitting, so their cuts see the original allocation cone.
				SigSpec done_sig;
				bool has_done = match_exclusive_done(rg, done_sig);

				XbarCand gx;
				bool have_gather = false;
				for (auto &cand : collect_exclusive_gather_cands(rg.nb)) {
					if (walk_exhausted() || eval_exhausted())
						break;
					if (cand.sig == rg.dsel_sig || root_claimed(cand.sig))
						continue;
					log_debug("ffa: try excl-gather cand %s (%d bits) for region %s\n",
					          cand.name.c_str(), GetSize(cand.sig), rg.dsel_name.c_str());
					if (match_exclusive_gather(rg, cand, done_sig, has_done, gx)) {
						have_gather = true;
						break;
					}
				}

				// Exclusive: clog2(nb+1)-bit ranks. Prefer thermometer scan for
				// small nb (shallower mapped LoL); binary sat-log otherwise.
				int cnt_w = clog2_int(rg.nb + 1);
				vector<SigBit> leader, grant;
				vector<SigSpec> slot, therm;
				bool use_therm = rg.nb <= max_therm_nb;
				if (use_therm)
					emit_scan_exclusive_therm(rg, leader, therm, grant, slot, cnt_w);
				else
					emit_scan_exclusive_bin(rg, leader, slot, grant, cnt_w);

				SigSpec new_dsel = emit_dsel_exclusive(rg, grant, slot, cnt_w);
				connect_driven(rg.dsel_sig, new_dsel, rg.anchor, "ffa_dangling");
				claim_region(rg.dsel_sig, rg.dsel_cut_cells);
				regions_rewritten++;

				log("  %s: %s <- first_fit_alloc(en=%s, exclusive nb=%d%s, %s)\n",
				    log_id(module), rg.dsel_name.c_str(), log_signal(rg.en_sig), rg.nb,
				    rg.exclusive_and2 ? ", and2" : "",
				    rg.msb_first ? "MSB-first" : "LSB-first");

				if (has_done) {
					SigSpec new_done = emit_exclusive_done(rg, grant);
					int dn = connect_driven(done_sig, new_done, rg.anchor, "ffa_done_dangling");
					log("    + exclusive grant/done: %s [%d bit(s) re-driven]\n",
					    log_signal(done_sig), dn);
				}

				if (have_gather) {
					log_assert(rg.exclusive && gx.identity && gx.a == gx.slot_w);
					SigSpec new_g = emit_exclusive_gather(rg, gx, grant, slot, cnt_w,
					                                      use_therm ? &therm : nullptr);
					int dn = connect_driven(gx.sig, new_g, gx.anchor, "ffa_xbar_dangling");
					claim_region(gx.sig, gx.cut_cells);
					log("    + exclusive identity gather: %s [slots=%d, slot_w=%d, %d bit(s) re-driven]\n",
					    gx.name.c_str(), gx.nb, gx.slot_w, dn);
				}
				continue;
			}

			// Find a sibling xbar root that shares this scan.
			XbarCand xb;
			bool have_xbar = false;
			for (auto &cand : roots) {
				if (cand.sig == rg.dsel_sig)
					continue;
				if (root_claimed(cand.sig))
					continue;
				// xbar bits must split evenly into 2^W per-slot blocks.
				if (GetSize(cand.sig) % (1 << rg.field_w) != 0)
					continue;
				log_debug("ffa: try xbar cand %s (%d bits) for region %s\n",
				          cand.name.c_str(), GetSize(cand.sig), rg.dsel_name.c_str());
				if (match_xbar(rg, BusCand{cand.sig, cand.name, cand.n, cand.elem}, xb)) {
					have_xbar = true;
					break;
				}
			}

			// Emit the shared scan once. Prefer thermometer when the max
			// leader count (min(n, 2^c)) fits max_therm_nb.
			int therm_nb = std::min(rg.n, 1 << rg.c);
			bool use_therm = therm_nb >= 1 && therm_nb <= max_therm_nb;
			int cnt_w = use_therm ? clog2_int(therm_nb + 1) : clog2_int(rg.n + 1);
			vector<SigBit> leader;
			vector<SigSpec> slot, therm, cat_lane;
			SigSpec total;
			emit_scan(rg, leader, slot, total, cnt_w, cat_lane,
			          use_therm ? &therm : nullptr, use_therm ? therm_nb : 0);

			SigSpec new_dsel = emit_dsel(rg, leader, slot, total, cnt_w);
			connect_driven(rg.dsel_sig, new_dsel, rg.anchor, "ffa_dangling");
			claim_region(rg.dsel_sig, rg.dsel_cut_cells);
			regions_rewritten++;

			log("  %s: %s <- first_fit_alloc(en=%s%s, cat=%dx%d, %s%s%s)\n",
			    log_id(module), rg.dsel_name.c_str(),
			    log_signal(rg.en_sig),
			    rg.has_bc ? stringf(", bc=%s", log_signal(rg.bc_sig)).c_str() : "",
			    rg.n, rg.c, rg.msb_first ? "MSB-first" : "LSB-first",
			    rg.coalesce ? ", coalesce" : "",
			    use_therm ? stringf(", therm_nb=%d", therm_nb).c_str() : "");

			if (have_xbar) {
				// Thermometer slot==s only if every xbar slot index fits.
				bool xbar_therm = use_therm && xb.nb <= therm_nb;
				SigSpec new_xbar = emit_xbar(rg, xb, leader, slot, cnt_w,
				                             xbar_therm ? &therm : nullptr);
				int dn = connect_driven(xb.sig, new_xbar, xb.anchor, "ffa_xbar_dangling");
				claim_region(xb.sig, xb.cut_cells);
				log("    + xbar field gather: %s [slots=%d, slot_w=%d, attr=%dx%d, %d bit(s) re-driven]\n",
				    xb.name.c_str(), xb.nb, xb.slot_w, rg.n, xb.a, dn);
			}
		}

		// Gather-rooted regions (no explicit dsel bus). Run after the dsel
		// path so an exclusive gather that IS reachable from a dsel root is
		// claimed there first and not re-attempted here.
		run_gather_rooted();
	}
};

struct OptFirstFitAllocPass : public Pass {
	OptFirstFitAllocPass() : Pass("opt_first_fit_alloc",
		"rewrite greedy first-fit resource allocators into log-depth scans") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_first_fit_alloc [options] [selection]\n");
		log("\n");
		log("This pass uses functional fingerprinting to detect combinational regions\n");
		log("that implement a greedy first-fit resource allocator: enabled request\n");
		log("lanes are scanned in priority order and the first lane of each category\n");
		log("(a 'leader') is assigned the next free slot, while later lanes of the\n");
		log("same category (and broadcast lanes) inherit that slot. An exclusive\n");
		log("saturating variant (no category/broadcast) is also recognized: each\n");
		log("enabled lane takes the next free slot until a learned slot budget is\n");
		log("exhausted, after which later requesters get rank 0. Its per-slot data\n");
		log("gather (slot_data[s] = data[leader at s]) is rewritten as an identity\n");
		log("gather driven from the same prefix-count scan.\n");
		log("\n");
		log("The serial loop-carried taken[]/done[] scan produced by the RTL is\n");
		log("replaced with a log-depth network: a shared prefix-OR of enables,\n");
		log("per-category prefix-OR leadership (small keys), a thermometer or\n");
		log("parallel-prefix slot assignment, and a rank gather. Where a per-slot\n");
		log("field table (an 'xbar') is driven from the same allocation, it is\n");
		log("rewritten as a shared per-slot field gather driven from the same scan.\n");
		log("\n");
		log("Category/coalesce prefix-sums prefer a thermometer encoding when the\n");
		log("max leader count fits -max thermometer budget; otherwise they are\n");
		log("emitted as linear $add cascades so a subsequent opt_parallel_prefix\n");
		log("pass rebuilds them into shared log-depth networks.\n");
		log("\n");
		log("A first-fit allocator consumed only as a per-slot data gather (with\n");
		log("no explicit per-lane rank bus), optionally buried under guard muxes\n");
		log("(an FSM case / per-entry hit mux) or read through an entry-side\n");
		log("compaction, is recognized by a gather-rooted anchor and rewritten\n");
		log("into the same log-depth exclusive scan + identity gather.\n");
		log("\n");
		log("    -min-width N, -max-width N\n");
		log("        lane-count range to consider (default 4..64).\n");
		log("\n");
		log("    -no-gather-root\n");
		log("        disable the gather-rooted anchor (dsel-rooted matching only).\n");
		log("\n");
		log("    -gather-root\n");
		log("        re-enable the gather-rooted anchor (default).\n");
		log("\n");
		log("    -max-therm N\n");
		log("        max slot count for the thermometer prefix encoding (default 8);\n");
		log("        wider scans fall back to a saturating binary count.\n");
		log("\n");
		log("    -walk-budget N, -eval-budget N, -attempt-budget N\n");
		log("        per-module work limits for the candidate search.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_FIRST_FIT_ALLOC pass (greedy first-fit allocator rewrite).\n");

		int min_n = 4, max_n = 64;
		int max_therm_nb = -1;
		int64_t walk_budget = -1, eval_budget = -1, attempt_budget = -1;
		bool gather_root = true;
		bool dbg_compact = false;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-no-gather-root" || args[argidx] == "-no_gather_root") {
				gather_root = false;
				continue;
			}
			if (args[argidx] == "-gather-root" || args[argidx] == "-gather_root") {
				gather_root = true;
				continue;
			}
			if (args[argidx] == "-dbg-compact") {
				dbg_compact = true;
				continue;
			}
			if ((args[argidx] == "-min-width" || args[argidx] == "-min_width") && argidx + 1 < args.size()) {
				min_n = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-width" || args[argidx] == "-max_width") && argidx + 1 < args.size()) {
				max_n = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-therm" || args[argidx] == "-max_therm") && argidx + 1 < args.size()) {
				max_therm_nb = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-walk-budget" || args[argidx] == "-walk_budget") && argidx + 1 < args.size()) {
				walk_budget = std::stoll(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-eval-budget" || args[argidx] == "-eval_budget") && argidx + 1 < args.size()) {
				eval_budget = std::stoll(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-attempt-budget" || args[argidx] == "-attempt_budget") && argidx + 1 < args.size()) {
				attempt_budget = std::stoll(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_regions = 0;
		int total_cells = 0;
		for (auto module : design->selected_modules()) {
			OptFirstFitAllocWorker worker(module);
			worker.min_n = min_n;
			worker.max_n = max_n;
			worker.gather_root = gather_root;
			worker.dbg_compact = dbg_compact;
			if (max_therm_nb >= 0)
				worker.max_therm_nb = max_therm_nb;
			if (walk_budget > 0)
				worker.walk_budget = walk_budget;
			if (eval_budget > 0)
				worker.eval_budget = eval_budget;
			if (attempt_budget > 0)
				worker.attempt_budget = attempt_budget;
			worker.run();
			total_regions += worker.regions_rewritten;
			total_cells += worker.cells_added;
		}

		log("Rewrote %d first-fit alloc region(s); emitted %d new cell(s).\n",
		    total_regions, total_cells);

		if (total_regions)
			Yosys::run_pass("clean -purge");
	}
} OptFirstFitAllocPass;

PRIVATE_NAMESPACE_END
