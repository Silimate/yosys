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
 *  WHATSOEVER RESULTING FROM LOSS OF USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/consteval.h"
#include <queue>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static int clog2_int(int x)
{
	int r = 0;
	while ((1 << r) < x) r++;
	return r;
}

static Const u64_const(uint64_t pattern, int width)
{
	std::vector<State> bits(width, State::S0);
	for (int i = 0; i < width && i < 64; i++)
		if ((pattern >> i) & 1ULL) bits[i] = State::S1;
	return Const(bits);
}

static int popcount_const(const Const &c, int width)
{
	int count = 0;
	auto bits = c.to_bits();
	for (int i = 0; i < width; i++)
		if (i < GetSize(bits) && bits[i] == State::S1) count++;
	return count;
}

static Const thermometer_const(int ones, int width)
{
	std::vector<State> bits(width, State::S0);
	for (int i = 0; i < width && i < ones; i++)
		bits[i] = State::S1;
	return Const(bits);
}

struct OptCompactPackWorker {
	Module *module;
	SigMap sigmap;

	dict<SigBit, Cell*> bit_to_driver;
	dict<SigBit, pool<Cell*>> bit_consumers;
	pool<SigBit> input_port_bits;
	pool<Cell*> sequential_cells;

	int min_width = 4;
	int max_width = 128;

	int candidates_seen = 0;
	int high_candidates_seen = 0;
	int high_cone_matches = 0;
	int high_fingerprint_matches = 0;
	int regions_rewritten = 0;
	int cells_added = 0;
	int max_popcount_depth = 0;

	OptCompactPackWorker(Module *m) : module(m), sigmap(m) { build_indexes(); }

	bool is_sequential(Cell *c)
	{
		return c->type.in(
			ID($ff), ID($dff), ID($dffe), ID($adff), ID($adffe),
			ID($sdff), ID($sdffe), ID($sdffce), ID($dffsr), ID($dffsre),
			ID($_DFF_P_), ID($_DFF_N_),
			ID($_DFFE_PP_), ID($_DFFE_PN_), ID($_DFFE_NP_), ID($_DFFE_NN_),
			ID($_DFF_PP0_), ID($_DFF_PP1_), ID($_DFF_PN0_), ID($_DFF_PN1_),
			ID($_DFF_NP_), ID($_DFF_NN_), ID($_DFF_NP0_), ID($_DFF_NP1_),
			ID($_DFF_NN0_), ID($_DFF_NN1_),
			ID($dlatch), ID($adlatch), ID($dlatchsr),
			ID($mem), ID($mem_v2), ID($meminit), ID($meminit_v2),
			ID($memrd), ID($memrd_v2), ID($memwr), ID($memwr_v2),
			ID($fsm),
			ID($assert), ID($assume), ID($cover), ID($live), ID($fair),
			ID($print), ID($check),
			ID($anyconst), ID($anyseq), ID($allconst), ID($allseq),
			ID($initstate));
	}

	void build_indexes()
	{
		for (auto cell : module->cells()) {
			if (is_sequential(cell)) {
				sequential_cells.insert(cell);
				continue;
			}
			for (auto &conn : cell->connections()) {
				if (cell->output(conn.first)) {
					for (auto bit : sigmap(conn.second))
						if (bit.wire) bit_to_driver[bit] = cell;
				} else if (cell->input(conn.first)) {
					for (auto bit : sigmap(conn.second))
						if (bit.wire) bit_consumers[bit].insert(cell);
				}
			}
		}

		for (auto wire : module->wires()) {
			if (!wire->port_input) continue;
			for (auto bit : sigmap(wire))
				input_port_bits.insert(bit);
		}
	}

	bool get_cone(SigSpec from, pool<Cell*> &cone_cells, pool<SigBit> &leaf_bits,
	              int max_cone_cells, int max_leaf_bits)
	{
		pool<SigBit> visited;
		std::queue<SigBit> worklist;

		for (auto bit : sigmap(from)) {
			if (!bit.wire) continue;
			if (visited.insert(bit).second) worklist.push(bit);
		}

		while (!worklist.empty()) {
			SigBit bit = worklist.front();
			worklist.pop();

			if (input_port_bits.count(bit)) {
				leaf_bits.insert(bit);
				if (GetSize(leaf_bits) > max_leaf_bits) return false;
				continue;
			}

			auto it = bit_to_driver.find(bit);
			if (it == bit_to_driver.end()) {
				leaf_bits.insert(bit);
				if (GetSize(leaf_bits) > max_leaf_bits) return false;
				continue;
			}

			Cell *drv = it->second;
			if (sequential_cells.count(drv)) {
				leaf_bits.insert(bit);
				if (GetSize(leaf_bits) > max_leaf_bits) return false;
				continue;
			}

			if (!cone_cells.insert(drv).second) continue;
			if (GetSize(cone_cells) > max_cone_cells) return false;

			for (auto &conn : drv->connections()) {
				if (!drv->input(conn.first)) continue;
				for (auto in_bit : sigmap(conn.second)) {
					if (!in_bit.wire) continue;
					if (visited.insert(in_bit).second) worklist.push(in_bit);
				}
			}
		}

		return true;
	}

	vector<Const> gen_test_vectors(int width)
	{
		vector<Const> vectors;

		if (width <= 8) {
			for (int mask = 0; mask < (1 << width); mask++)
				vectors.push_back(u64_const(mask, width));
			return vectors;
		}

		vectors.push_back(u64_const(0, width));
		vectors.push_back(Const(State::S1, width));

		for (int i = 0; i < width; i++) {
			std::vector<State> bits(width, State::S0);
			bits[i] = State::S1;
			vectors.push_back(Const(bits));
		}

		for (int k = 1; k <= width; k++) {
			std::vector<State> prefix(width, State::S0);
			std::vector<State> suffix(width, State::S0);
			for (int i = 0; i < k; i++) {
				prefix[i] = State::S1;
				suffix[width - 1 - i] = State::S1;
			}
			vectors.push_back(Const(prefix));
			vectors.push_back(Const(suffix));
		}

		for (int phase = 0; phase < 2; phase++) {
			std::vector<State> bits(width, State::S0);
			for (int i = 0; i < width; i++)
				if ((i & 1) == phase) bits[i] = State::S1;
			vectors.push_back(Const(bits));
		}

		uint64_t state = 0x9e3779b97f4a7c15ULL ^ uint64_t(width);
		for (int v = 0; v < 32; v++) {
			std::vector<State> bits(width, State::S0);
			for (int i = 0; i < width; i++) {
				state ^= state << 7;
				state ^= state >> 9;
				if (state & 1ULL) bits[i] = State::S1;
			}
			vectors.push_back(Const(bits));
		}

		return vectors;
	}

	bool cone_depends_only_on(SigSpec from, const pool<SigBit> &allowed_bits)
	{
		pool<SigBit> visited;
		std::queue<SigBit> worklist;

		for (auto bit : sigmap(from)) {
			if (!bit.wire) continue;
			if (visited.insert(bit).second) worklist.push(bit);
		}

		while (!worklist.empty()) {
			SigBit bit = worklist.front();
			worklist.pop();

			if (allowed_bits.count(bit)) continue;
			if (input_port_bits.count(bit)) return false;

			auto it = bit_to_driver.find(bit);
			if (it == bit_to_driver.end()) continue;

			Cell *drv = it->second;
			if (sequential_cells.count(drv)) return false;

			for (auto &conn : drv->connections()) {
				if (!drv->input(conn.first)) continue;
				for (auto in_bit : sigmap(conn.second)) {
					if (!in_bit.wire) continue;
					if (visited.insert(in_bit).second) worklist.push(in_bit);
				}
			}
		}

		return true;
	}

	bool fingerprints_as_self_compact(SigSpec in_sig, SigSpec out_sig, int width)
	{
		ConstEval ce(module);
		for (auto &v : gen_test_vectors(width)) {
			ce.push();
			ce.set(in_sig, v);
			SigSpec actual = out_sig;
			SigSpec undef;
			bool ok = ce.eval(actual, undef);
			ce.pop();

			if (!ok || !actual.is_fully_const())
				return false;

			Const expected = thermometer_const(popcount_const(v, width), width);
			if (actual.as_const() != expected)
				return false;
		}

		return true;
	}

	Const high_masked_pack_const(const Const &disable, const Const &data, int out_width, int active_width)
	{
		std::vector<State> out(out_width, State::S0);
		auto d_bits = disable.to_bits();
		auto x_bits = data.to_bits();

		int enabled_above = 0;
		for (int i = active_width - 1; i >= 0; i--) {
			State disabled = i < GetSize(d_bits) ? d_bits[i] : State::S0;
			if (disabled == State::S1)
				continue;

			int data_idx = active_width - 1 - enabled_above;
			out[i] = data_idx < GetSize(x_bits) ? x_bits[data_idx] : State::S0;
			enabled_above++;
		}

		return Const(out);
	}

	Const extend_active_const(const Const &active, int full_width, int active_width, State fill)
	{
		std::vector<State> bits(full_width, fill);
		auto active_bits = active.to_bits();
		for (int i = 0; i < active_width && i < full_width; i++)
			bits[i] = i < GetSize(active_bits) ? active_bits[i] : State::S0;
		return Const(bits);
	}

	vector<Const> gen_data_vectors(int width)
	{
		vector<Const> vectors;
		vectors.push_back(u64_const(0, width));
		vectors.push_back(Const(State::S1, width));

		for (int i = 0; i < width; i++) {
			std::vector<State> bits(width, State::S0);
			bits[i] = State::S1;
			vectors.push_back(Const(bits));
		}

		for (int phase = 0; phase < 2; phase++) {
			std::vector<State> bits(width, State::S0);
			for (int i = 0; i < width; i++)
				if ((i & 1) == phase) bits[i] = State::S1;
			vectors.push_back(Const(bits));
		}

		uint64_t state = 0xd1b54a32d192ed03ULL ^ uint64_t(width);
		for (int v = 0; v < 16; v++) {
			std::vector<State> bits(width, State::S0);
			for (int i = 0; i < width; i++) {
				state ^= state << 13;
				state ^= state >> 7;
				state ^= state << 17;
				if (state & 1ULL) bits[i] = State::S1;
			}
			vectors.push_back(Const(bits));
		}

		return vectors;
	}

	bool fingerprints_as_high_masked_pack(SigSpec disable_sig, SigSpec data_sig,
	                                      SigSpec out_sig, int out_width, int active_width)
	{
		ConstEval ce(module);
		vector<Const> disable_vectors = gen_test_vectors(active_width);
		vector<Const> data_vectors = gen_data_vectors(active_width);

		for (auto &d : disable_vectors) {
			for (auto &x : data_vectors) {
				for (State d_fill : {State::S0, State::S1}) {
					for (State x_fill : {State::S0, State::S1}) {
						ce.push();
						ce.set(disable_sig, extend_active_const(d, GetSize(disable_sig),
						                                        active_width, d_fill));
						ce.set(data_sig, extend_active_const(x, GetSize(data_sig),
						                                     active_width, x_fill));

						SigSpec actual = out_sig;
						SigSpec undef;
						bool ok = ce.eval(actual, undef);
						ce.pop();

						if (!ok || !actual.is_fully_const())
							return false;

						Const expected = high_masked_pack_const(d, x, out_width, active_width);
						if (actual.as_const() != expected)
							return false;
					}
				}
			}
		}

		return true;
	}

	struct CountNode {
		SigSpec sig;
		int depth;
	};

	SigSpec widened_bit(SigBit bit, int width)
	{
		SigSpec out;
		out.append(bit);
		if (width > 1)
			out.append(SigSpec(State::S0, width - 1));
		return out;
	}

	SigSpec emit_popcount(SigSpec in_sig, int width)
	{
		int count_width = clog2_int(width + 1);
		vector<CountNode> level;
		for (auto bit : in_sig)
			level.push_back({widened_bit(bit, count_width), 0});

		while (GetSize(level) > 1) {
			vector<CountNode> next;
			for (int i = 0; i < GetSize(level); i += 2) {
				if (i + 1 == GetSize(level)) {
					next.push_back(level[i]);
					continue;
				}
				SigSpec sum = module->Add(NEW_ID, level[i].sig, level[i + 1].sig);
				int depth = std::max(level[i].depth, level[i + 1].depth) + 1;
				next.push_back({sum.extract(0, count_width), depth});
				cells_added++;
				if (depth > max_popcount_depth) max_popcount_depth = depth;
			}
			level = std::move(next);
		}

		return level.empty() ? SigSpec(State::S0, count_width) : level.front().sig.extract(0, count_width);
	}

	SigSpec zero_extend(SigSpec sig, int width)
	{
		if (GetSize(sig) >= width)
			return sig.extract(0, width);
		sig.append(SigSpec(State::S0, width - GetSize(sig)));
		return sig;
	}

	SigSpec emit_self_compact(Wire *in_wire, int width)
	{
		int count_width = clog2_int(width + 1);
		SigSpec count = emit_popcount(sigmap(SigSpec(in_wire)), width);
		SigSpec out;

		for (int i = 0; i < width; i++) {
			SigSpec gt = module->Gt(NEW_ID, count, SigSpec(Const(i, count_width)));
			out.append(gt[0]);
			cells_added++;
		}

		return out;
	}

	SigSpec emit_high_masked_pack(Wire *disable_wire, Wire *data_wire, int out_width, int active_width)
	{
		int count_width = clog2_int(active_width + 1);
		SigSpec disable = sigmap(SigSpec(disable_wire)).extract(0, active_width);
		SigSpec data = sigmap(SigSpec(data_wire)).extract(0, active_width);

		vector<SigBit> enable;
		for (int i = 0; i < active_width; i++) {
			SigSpec en = module->Not(NEW_ID, disable[i]);
			enable.push_back(en[0]);
			cells_added++;
		}

		SigSpec out;
		for (int i = 0; i < active_width; i++) {
			SigSpec suffix;
			for (int k = i + 1; k < active_width; k++)
				suffix.append(enable[k]);

			SigSpec count = suffix.empty()
				? SigSpec(Const(0, count_width))
				: zero_extend(emit_popcount(suffix, GetSize(suffix)), count_width);

			SigSpec pmux_b, pmux_s;
			for (int data_idx = i; data_idx < active_width; data_idx++) {
				int needed_count = active_width - 1 - data_idx;
				SigSpec eq = module->Eq(NEW_ID, count, SigSpec(Const(needed_count, count_width)));
				SigSpec sel = module->And(NEW_ID, SigSpec(enable[i]), eq);
				pmux_b.append(data[data_idx]);
				pmux_s.append(sel[0]);
				cells_added += 2;
			}

			SigSpec bit = module->Pmux(NEW_ID, State::S0, pmux_b, pmux_s);
			out.append(bit[0]);
			cells_added++;
		}

		if (out_width > active_width)
			out.append(SigSpec(State::S0, out_width - active_width));

		return out;
	}

	int nonzero_output_width(Wire *out_wire)
	{
		SigSpec out = sigmap(SigSpec(out_wire));
		for (int i = GetSize(out) - 1; i >= 0; i--)
			if (out[i] != State::S0)
				return i + 1;
		return 0;
	}

	bool output_drivers_are_isolated(Wire *out_wire, dict<Cell*, pool<IdString>> &ports_to_disconnect)
	{
		pool<SigBit> target_bits;
		SigSpec out_sig = sigmap(SigSpec(out_wire));
		for (auto bit : out_sig)
			if (bit.wire) target_bits.insert(bit);

		for (auto bit : out_sig) {
			if (!bit.wire) continue;
			auto it = bit_to_driver.find(bit);
			if (it == bit_to_driver.end()) continue;

			Cell *driver = it->second;
			bool found_port = false;
			for (auto &conn : driver->connections()) {
				if (!driver->output(conn.first)) continue;
				SigSpec driven = sigmap(conn.second);
				bool contains_bit = false;
				for (auto driven_bit : driven) {
					if (driven_bit == bit)
						contains_bit = true;
					if (driven_bit.wire && !target_bits.count(driven_bit)) {
						if (driven_bit.wire->port_output)
							return false;
						if (bit_consumers.count(driven_bit) && !bit_consumers.at(driven_bit).empty())
							return false;
					}
				}
				if (contains_bit) {
					ports_to_disconnect[driver].insert(conn.first);
					found_port = true;
				}
			}
			if (!found_port) return false;
		}

		return true;
	}

	void disconnect_old_output_drivers(const dict<Cell*, pool<IdString>> &ports_to_disconnect)
	{
		for (auto &kv : ports_to_disconnect) {
			Cell *cell = kv.first;
			for (auto port : kv.second) {
				int width = GetSize(cell->getPort(port));
				Wire *dangling = module->addWire(NEW_ID2_SUFFIX("compact_dangling"), width);
				cell->setPort(port, dangling);
			}
		}
	}

	struct Rewrite {
		Wire *out_wire;
		Wire *in_wire;
		Wire *data_wire;
		int active_width;
		bool high_masked_pack;
		dict<Cell*, pool<IdString>> ports_to_disconnect;
	};

	void run()
	{
		vector<Wire*> wires_snapshot(module->wires().begin(), module->wires().end());
		vector<Rewrite> rewrites;
		pool<Wire*> claimed_outputs;

		int max_cone_cells = std::max(256, max_width * 32);
		int max_leaf_bits = max_width + 8;

		for (Wire *out_wire : wires_snapshot) {
			if (!out_wire->port_output || out_wire->port_input) continue;
			if (out_wire->width < min_width || out_wire->width > max_width) continue;

			pool<Cell*> cone_cells;
			pool<SigBit> leaf_bits;
			if (!get_cone(SigSpec(out_wire), cone_cells, leaf_bits, max_cone_cells, max_leaf_bits))
				continue;
			if (cone_cells.empty()) continue;

			candidates_seen++;

			pool<SigBit> cone_bits = leaf_bits;
			for (Cell *cell : cone_cells) {
				for (auto &conn : cell->connections()) {
					if (!cell->output(conn.first)) continue;
					for (auto bit : sigmap(conn.second))
						if (bit.wire) cone_bits.insert(bit);
				}
			}

			vector<Wire*> input_candidates;
			for (Wire *in_wire : wires_snapshot) {
				if (in_wire == out_wire) continue;
				if (in_wire->width != out_wire->width) continue;

				bool all_in_cone = true;
				bool any_input = false;
				for (auto bit : sigmap(SigSpec(in_wire))) {
					if (!bit.wire || !cone_bits.count(bit)) {
						all_in_cone = false;
						break;
					}
					if (input_port_bits.count(bit))
						any_input = true;
				}
				if (all_in_cone && any_input)
					input_candidates.push_back(in_wire);
			}

			std::sort(input_candidates.begin(), input_candidates.end(), [](Wire *a, Wire *b) {
				if (a->port_input != b->port_input) return a->port_input > b->port_input;
				return a->name.str() < b->name.str();
			});

			for (Wire *in_wire : input_candidates) {
				SigSpec in_sig = sigmap(SigSpec(in_wire));
				SigSpec out_sig = sigmap(SigSpec(out_wire));
				pool<SigBit> in_bits;
				for (auto bit : in_sig)
					if (bit.wire) in_bits.insert(bit);

				if (!cone_depends_only_on(out_sig, in_bits)) continue;
				if (!fingerprints_as_self_compact(in_sig, out_sig, out_wire->width)) continue;

				dict<Cell*, pool<IdString>> ports_to_disconnect;
				if (!output_drivers_are_isolated(out_wire, ports_to_disconnect)) continue;
				if (claimed_outputs.count(out_wire)) continue;

				log("  %s: %s <- self_compact(%s) [width=%d]\n",
				    log_id(module), log_id(out_wire), log_id(in_wire), out_wire->width);
				rewrites.push_back({out_wire, in_wire, nullptr, out_wire->width, false,
				                    std::move(ports_to_disconnect)});
				claimed_outputs.insert(out_wire);
				break;
			}

			if (claimed_outputs.count(out_wire)) continue;

			vector<Wire*> port_inputs;
			int out_active_limit = nonzero_output_width(out_wire);
			if (out_active_limit < min_width) continue;
			for (Wire *in_wire : wires_snapshot) {
				if (!in_wire->port_input || in_wire == out_wire) continue;
				if (in_wire->width < min_width) continue;
				port_inputs.push_back(in_wire);
			}

			for (Wire *disable_wire : port_inputs) {
				if (claimed_outputs.count(out_wire)) break;
				for (Wire *data_wire : port_inputs) {
					if (data_wire == disable_wire) continue;

					int max_active = std::min({out_active_limit, disable_wire->width,
					                           data_wire->width, max_width});
					for (int active_width = max_active; active_width >= min_width; active_width--) {
						high_candidates_seen++;
						SigSpec disable_sig = sigmap(SigSpec(disable_wire));
						SigSpec data_sig = sigmap(SigSpec(data_wire));
						SigSpec out_sig = sigmap(SigSpec(out_wire));

						pool<SigBit> allowed_bits;
						for (auto bit : disable_sig)
							if (bit.wire) allowed_bits.insert(bit);
						for (auto bit : data_sig)
							if (bit.wire) allowed_bits.insert(bit);

						if (!cone_depends_only_on(out_sig, allowed_bits)) continue;
						high_cone_matches++;
						if (!fingerprints_as_high_masked_pack(disable_sig, data_sig,
						                                      out_sig, out_wire->width,
						                                      active_width)) continue;
						high_fingerprint_matches++;

						dict<Cell*, pool<IdString>> ports_to_disconnect;
						if (!output_drivers_are_isolated(out_wire, ports_to_disconnect)) continue;

						log("  %s: %s <- high_masked_pack(disable=%s, data=%s) [active_width=%d, out_width=%d]\n",
						    log_id(module), log_id(out_wire), log_id(disable_wire),
						    log_id(data_wire), active_width, out_wire->width);
						rewrites.push_back({out_wire, disable_wire, data_wire, active_width,
						                    true, std::move(ports_to_disconnect)});
						claimed_outputs.insert(out_wire);
						break;
					}
					if (claimed_outputs.count(out_wire)) break;
				}
			}
		}

		for (auto &rewrite : rewrites) {
			SigSpec compact = rewrite.high_masked_pack
				? emit_high_masked_pack(rewrite.in_wire, rewrite.data_wire,
				                        rewrite.out_wire->width, rewrite.active_width)
				: emit_self_compact(rewrite.in_wire, rewrite.out_wire->width);
			disconnect_old_output_drivers(rewrite.ports_to_disconnect);
			module->connect(SigSpec(rewrite.out_wire), compact);
			regions_rewritten++;
		}
	}
};

struct OptCompactPackPass : public Pass {
	OptCompactPackPass() : Pass("opt_compact_pack",
		"detect and rewrite compact-pack regions") {}

	void help() override
	{
		log("\n");
		log("    opt_compact_pack [options] [selection]\n");
		log("\n");
		log("This pass detects combinational regions that implement compact-pack\n");
		log("idioms. The first recognized function is boolean self-compaction:\n");
		log("\n");
		log("    out[j] = popcount(in) > j\n");
		log("\n");
		log("This is the lowered form of loops such as `if (in[i]) out[idx++] = 1'b1;`\n");
		log("with zero-filled output. The pass replaces the long loop-carried add and\n");
		log("dynamic-write cone with a balanced popcount tree plus comparators.\n");
		log("\n");
		log("The second recognized function is a high-side masked data pack from loops\n");
		log("that decrement an index when an output bit is enabled:\n");
		log("\n");
		log("    if (!disable[i]) out[i] = data[idx--]\n");
		log("\n");
		log("The pass replaces the long subtract chain and per-bit dynamic reads with\n");
		log("suffix popcount/rank logic and one-hot pmux data routing.\n");
		log("\n");
		log("    -max-width N\n");
		log("        maximum input/output bus width to consider (default 128).\n");
		log("\n");
		log("    -min-width N\n");
		log("        minimum input/output bus width to consider (default 4).\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_COMPACT_PACK pass (compact-pack rewrites).\n");

		int min_width = 4;
		int max_width = 128;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-max-width" && argidx + 1 < args.size()) {
				max_width = std::stoi(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-min-width" && argidx + 1 < args.size()) {
				min_width = std::stoi(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_candidates = 0;
		int total_high_candidates = 0;
		int total_high_cone = 0;
		int total_high_fingerprint = 0;
		int total_regions = 0;
		int total_cells = 0;
		int total_depth = 0;

		for (auto module : design->selected_modules()) {
			OptCompactPackWorker worker(module);
			worker.min_width = min_width;
			worker.max_width = max_width;
			worker.run();
			total_candidates += worker.candidates_seen;
			total_high_candidates += worker.high_candidates_seen;
			total_high_cone += worker.high_cone_matches;
			total_high_fingerprint += worker.high_fingerprint_matches;
			total_regions += worker.regions_rewritten;
			total_cells += worker.cells_added;
			total_depth = std::max(total_depth, worker.max_popcount_depth);
		}

		log("Checked %d output candidate region(s); rewrote %d compact-pack region(s); emitted %d new cell(s); max popcount depth %d.\n",
		    total_candidates, total_regions, total_cells, total_depth);
		log("Checked %d high-pack candidate(s); %d passed cone checks; %d passed fingerprints.\n",
		    total_high_candidates, total_high_cone, total_high_fingerprint);

		Yosys::run_pass("clean -purge");
	}
} OptCompactPackPass;

PRIVATE_NAMESPACE_END
