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
#include "kernel/celltypes.h"
#include <cmath>
#include <functional>
#include <vector>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "passes/silimate/unit_delay.h"

// Marks the incrementer/mux a carry-select rewrite emits so peepopt -muxorder
// (which would otherwise fold `s ? (a+1) : a` back into `a + s`, putting the
// late select on a wide ripple carry) leaves them alone.
static const IdString kAttrCarrySelect = ID(carry_select);

// How late a module's own input ports arrive, and how deep it is from those
// inputs to each output port. Keyed by module, then by port bit.
typedef dict<Module *, dict<SigBit, double>> HierArrival;

// Arrival walk that can see past the module boundary, given what the caller
// already worked out about the ports and the child instances below it.
struct HierTiming : FracDelayTiming {
	// Absolute arrival of this module's input port bits, empty for the top.
	const dict<SigBit, double> *port_arrival;
	// Arrival of bits a child instance drives; filled by the fixpoint below.
	dict<SigBit, double> inst_arrival;

	HierTiming(Module *m, const dict<SigBit, double> *port_arrival)
		: FracDelayTiming(m), port_arrival(port_arrival)
	{
		build_connectivity();
	}

	// A child instance is an unknown cell type, so the base walk already stops
	// at it; both it and an input port therefore arrive here.
	double start_arrival(SigBit bit) override
	{
		auto inst = inst_arrival.find(bit);
		if (inst != inst_arrival.end())
			return inst->second;
		if (port_arrival != nullptr && bit.wire != nullptr && bit.wire->port_input) {
			auto port = port_arrival->find(bit);
			if (port != port_arrival->end())
				return port->second;
		}
		return 0;
	}

	// Charge every bit a child instance drives the depth from that child's own
	// inputs to the matching output port, on top of the latest input reaching
	// the instance. Instances can chain (a carry out of one slice feeding the
	// next), so iterate to a fixpoint; arrivals only ever rise, and the bound
	// keeps a pathological chain from costing more than it can win.
	void resolve_instances(Design *design, const HierArrival &internal, int max_rounds)
	{
		for (int round = 0; round < max_rounds; round++) {
			bool changed = false;
			// Collect the whole round before applying it. Updating in place
			// would leave arrivals memoized against a half-updated map, so the
			// result depended on cell order rather than on the netlist.
			dict<SigBit, double> pending;
			reset_timing();
			for (auto cell : module->cells()) {
				Module *child = design->module(cell->type);
				if (child == nullptr)
					continue;
				auto depth = internal.find(child);
				if (depth == internal.end())
					continue;

				// Latest input reaching the instance, composed with the child's
				// own input-to-output depth. Per-output rather than per-cell, so
				// a shallow output is not charged a deep sibling's depth.
				double in_arrival = 0;
				for (auto &conn : cell->connections())
					if (cell->input(conn.first))
						in_arrival = std::max(in_arrival, arrival(conn.second));

				for (auto &conn : cell->connections()) {
					if (!cell->output(conn.first))
						continue;
					Wire *child_port = child->wire(conn.first);
					if (child_port == nullptr)
						continue;
					SigSpec child_bits = SigSpec(child_port);
					SigSpec parent_bits = sigmap(conn.second);
					for (int i = 0; i < GetSize(parent_bits); i++) {
						if (i >= GetSize(child_bits) || parent_bits[i].wire == nullptr)
							continue;
						double value = in_arrival + depth->second.at(child_bits[i], 0.0);
						if (value > std::max(inst_arrival.at(parent_bits[i], 0.0),
						                     pending.at(parent_bits[i], 0.0)) + 1e-9) {
							pending[parent_bits[i]] = value;
							changed = true;
						}
					}
				}
			}
			for (auto &update : pending)
				inst_arrival[update.first] = update.second;
			if (!changed)
				break;
		}
		reset_timing();
	}
};

struct OptCarrySelectWorker : FracDelayTiming {
	int max_narrow;
	int min_wide;
	double margin;
	// Input port arrivals handed down from the parent, null when not in
	// hierarchical mode (every port then reads as arriving at 0, as before).
	const dict<SigBit, double> *port_arrival = nullptr;
	const dict<SigBit, double> *inst_arrival = nullptr;

	int converted = 0;

	OptCarrySelectWorker(Module *m, int max_narrow, int min_wide, double margin)
		: FracDelayTiming(m), max_narrow(max_narrow), min_wide(min_wide), margin(margin)
	{
		for (auto cell : module->cells())
			for (auto &conn : cell->connections())
				if (cell->output(conn.first))
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							driver_map[bit] = cell;
	}

	// Same seeding as HierTiming, so the rewrite decision and the analysis that
	// produced the port arrivals agree on what "late" means.
	double start_arrival(SigBit bit) override
	{
		if (inst_arrival != nullptr) {
			auto inst = inst_arrival->find(bit);
			if (inst != inst_arrival->end())
				return inst->second;
		}
		if (port_arrival != nullptr && bit.wire != nullptr && bit.wire->port_input) {
			auto port = port_arrival->find(bit);
			if (port != port_arrival->end())
				return port->second;
		}
		return 0;
	}

	// Decision record so we never iterate over a mutating cell list.
	struct Plan {
		Cell *add;
		bool wide_is_a;
		int k;   // narrow width / split point
		int w;   // result width
	};

	bool qualifies(Cell *c, Plan &plan) {
		if (c->type != ID($add))
			return false;
		if (c->get_bool_attribute(kAttrCarrySelect))
			return false;
		if (c->getParam(ID::A_SIGNED).as_bool() || c->getParam(ID::B_SIGNED).as_bool())
			return false; // v1: unsigned operands only (exact zero-extension)

		int a_w = c->getParam(ID::A_WIDTH).as_int();
		int b_w = c->getParam(ID::B_WIDTH).as_int();
		int w = c->getParam(ID::Y_WIDTH).as_int();

		bool wide_is_a = a_w >= b_w;
		int narrow_w = std::min(a_w, b_w);
		int k = narrow_w;

		// Per-candidate trace (only wide adders, to keep -g output readable) so it
		// is easy to see why a given $add was/was not turned into carry-select form.
		bool show = w >= 32;
		auto reject = [&](const char *why) {
			if (show)
				log_debug("opt_carry_select: %s/%s reject(%s) a_w=%d b_w=%d y_w=%d k=%d\n",
				          log_id(module), log_id(c), why, a_w, b_w, w, k);
			return false;
		};

		if (k < 1 || k >= w)
			return reject("narrow-not-narrower");
		if (k > max_narrow)
			return reject("narrow-too-wide");
		if (w - k < min_wide)
			return reject("high-too-small");

		SigSpec wide_sig = c->getPort(wide_is_a ? ID::A : ID::B);
		SigSpec narrow_sig = c->getPort(wide_is_a ? ID::B : ID::A);

		double arr_wide = arrival(wide_sig);
		double arr_narrow = arrival(narrow_sig);
		if (arr_narrow <= arr_wide + margin) {
			if (show)
				log_debug("opt_carry_select: %s/%s reject(narrow-not-late) a_w=%d b_w=%d "
				          "y_w=%d k=%d arr_wide=%.2f arr_narrow=%.2f\n",
				          log_id(module), log_id(c), a_w, b_w, w, k, arr_wide, arr_narrow);
			return false; // no timing benefit: narrow operand is not the late one
		}

		if (show)
			log_debug("opt_carry_select: %s/%s accept a_w=%d b_w=%d y_w=%d k=%d "
			          "arr_wide=%.2f arr_narrow=%.2f\n",
			          log_id(module), log_id(c), a_w, b_w, w, k, arr_wide, arr_narrow);

		plan.add = c;
		plan.wide_is_a = wide_is_a;
		plan.k = k;
		plan.w = w;
		return true;
	}

	void apply(const Plan &plan) {
		Cell *cell = plan.add;
		int k = plan.k;
		int w = plan.w;
		std::string src = cell->get_src_attribute();

		SigSpec wide_sig = cell->getPort(plan.wide_is_a ? ID::A : ID::B);
		SigSpec narrow_sig = cell->getPort(plan.wide_is_a ? ID::B : ID::A);
		SigSpec y = cell->getPort(ID::Y);

		// Zero-extend the wide operand to the full result width.
		SigSpec wext = wide_sig;
		wext.extend_u0(w, /*is_signed=*/false);
		SigSpec wlow = wext.extract(0, k);
		SigSpec whigh = wext.extract(k, w - k);

		// Low add: produces the low k sum bits plus the carry into bit k.
		Wire *losum = module->addWire(NEW_ID2_SUFFIX("cs_lo"), k + 1);
		module->addAdd(NEW_ID2_SUFFIX("cs_lo_add"), wlow, narrow_sig, SigSpec(losum), /*is_signed=*/false, src);
		SigSpec losum_low = SigSpec(losum).extract(0, k);
		SigBit carry = SigSpec(losum)[k];

		// High part precomputed from the (early) wide operand, then selected by
		// the (late) low carry: hi = carry ? (whigh + 1) : whigh.
		Wire *hiinc = module->addWire(NEW_ID2_SUFFIX("cs_hi_inc"), w - k);
		Cell *inc = module->addAdd(NEW_ID2_SUFFIX("cs_hi_inc_add"), whigh, SigSpec(State::S1), SigSpec(hiinc), /*is_signed=*/false, src);
		inc->set_bool_attribute(kAttrCarrySelect);

		Wire *hi = module->addWire(NEW_ID2_SUFFIX("cs_hi"), w - k);
		Cell *mux = module->addMux(NEW_ID2_SUFFIX("cs_hi_mux"), /*A=*/whigh, /*B=*/SigSpec(hiinc), /*S=*/carry, SigSpec(hi), src);
		mux->set_bool_attribute(kAttrCarrySelect);

		// Reassemble result and drive the original adder output.
		SigSpec result = losum_low;
		result.append(SigSpec(hi));
		module->connect(y, result);
		module->remove(cell);
		converted++;
	}

	void run() {
		vector<Cell*> adds;
		for (auto cell : module->cells())
			if (cell->type == ID($add))
				adds.push_back(cell);

		vector<Plan> plans;
		for (auto c : adds) {
			Plan plan;
			if (qualifies(c, plan))
				plans.push_back(plan);
		}
		for (auto &plan : plans)
			apply(plan);
	}
};

// Modules with children before their parents, so a bottom-up walk can rely on
// every child already being measured. An instantiation cycle admits no such
// order and is broken arbitrarily: one module in it is measured before its
// child and reads that child's depth as 0, which under-estimates arrival and so
// loses rewrites rather than taking wrong ones.
static std::vector<Module *> modules_bottom_up(Design *design)
{
	// Built complete up front, and read through a copy below: recursing while a
	// range-for walks children[module] would rehash the dict under the loop.
	dict<Module *, std::vector<Module *>> children;
	for (auto module : design->modules()) {
		auto &kids = children[module];
		pool<Module *> seen;
		for (auto cell : module->cells())
			if (Module *child = design->module(cell->type))
				if (child != module && seen.insert(child).second)
					kids.push_back(child);
	}

	std::vector<Module *> order;
	pool<Module *> done, active;
	std::function<void(Module *)> visit = [&](Module *module) {
		if (done.count(module) || active.count(module))
			return;
		active.insert(module);
		std::vector<Module *> kids = children.at(module);
		for (auto child : kids)
			visit(child);
		active.erase(module);
		done.insert(module);
		order.push_back(module);
	};
	for (auto module : design->modules())
		visit(module);
	return order;
}

// Depth from each module's input ports to each of its output ports, measured
// bottom-up so an instance is charged what is actually inside it. This is the
// half a per-module walk cannot know: without it, a carry out of one slice
// feeding the next reads as arriving the instant the clock edge does.
static HierArrival measure_internal_depth(Design *design,
                                          const std::vector<Module *> &bottom_up, int max_rounds)
{
	HierArrival internal;
	for (auto module : bottom_up) {
		HierTiming timing(module, /*port_arrival=*/nullptr);
		timing.resolve_instances(design, internal, max_rounds);
		auto &depth = internal[module];
		for (auto wire : module->wires()) {
			if (!wire->port_output)
				continue;
			for (auto bit : SigSpec(wire))
				depth[bit] = timing.arrival_bit(bit);
		}
	}
	return internal;
}

// Absolute arrival of every module's input ports, pushed down from the parents.
// A module instantiated more than once keeps the *earliest* arrival each port
// ever sees, so a rewrite that only pays when the operand is late is never
// taken on the strength of one favourable instantiation.
static HierArrival seed_port_arrival(Design *design, const std::vector<Module *> &bottom_up,
                                     const HierArrival &internal, int max_rounds)
{
	HierArrival seeded;
	pool<Module *> instantiated;
	for (auto it = bottom_up.rbegin(); it != bottom_up.rend(); ++it) {
		Module *module = *it;
		// Held by value: the loop below inserts this module's children into
		// `seeded`, which would rehash and dangle a pointer into it.
		dict<SigBit, double> own_ports = seeded.at(module, dict<SigBit, double>());
		HierTiming timing(module, &own_ports);
		timing.resolve_instances(design, internal, max_rounds);

		for (auto cell : module->cells()) {
			Module *child = design->module(cell->type);
			if (child == nullptr)
				continue;

			// What this one instantiation implies for every child input port
			// bit. Bits it leaves unconnected arrive at 0 and have to be
			// carried as 0 rather than skipped, or a port that is late in one
			// instance and absent in another would keep the late value.
			dict<SigBit, double> this_inst;
			for (auto wire : child->wires())
				if (wire->port_input)
					for (auto bit : SigSpec(wire))
						this_inst[bit] = 0.0;
			for (auto &conn : cell->connections()) {
				if (!cell->input(conn.first))
					continue;
				Wire *child_port = child->wire(conn.first);
				if (child_port == nullptr)
					continue;
				SigSpec child_bits = SigSpec(child_port);
				SigSpec parent_bits = timing.sigmap(conn.second);
				for (int i = 0; i < GetSize(parent_bits) && i < GetSize(child_bits); i++)
					this_inst[child_bits[i]] = timing.arrival_bit(parent_bits[i]);
			}

			// The first instantiation sets the arrival and later ones can only
			// lower it, so a rewrite that only pays when the operand is late is
			// never taken on the strength of one favourable instantiation.
			bool first = instantiated.insert(child).second;
			dict<SigBit, double> child_ports = seeded.at(child, dict<SigBit, double>());
			for (auto &entry : this_inst)
				child_ports[entry.first] = first
					? entry.second
					: std::min(child_ports.at(entry.first, 0.0), entry.second);
			seeded[child] = child_ports;
		}
	}
	return seeded;
}

struct OptCarrySelectPass : public Pass {
	OptCarrySelectPass() : Pass("opt_carry_select",
		"decompose wide-early + narrow-late adders into carry-select form") {}

	void help() override {
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_carry_select [options] [selection]\n");
		log("\n");
		log("Rewrites a $add of the shape `wide_early + narrow_late` into a low add plus\n");
		log("a high carry-select. The low add absorbs the late, narrow operand and emits a\n");
		log("carry; the wide high half is precomputed from the early operand (as `hi` and\n");
		log("`hi + 1`) and selected by that carry through a single mux. This moves the wide\n");
		log("carry propagation onto the early operand, so the late operand only sees a\n");
		log("small add plus one mux instead of a full-width ripple carry.\n");
		log("\n");
		log("Only unsigned adders whose narrow operand arrives later (per a heuristic\n");
		log("logic-depth model) than the wide operand are rewritten, so adders that would\n");
		log("not benefit are left untouched. Emitted cells are tagged so peepopt -muxorder\n");
		log("does not fold the carry-select back into a late-carry ripple adder.\n");
		log("\n");
		log("    -max-narrow N\n");
		log("        only rewrite when the narrow operand width is <= N (default 16).\n");
		log("\n");
		log("    -min-wide N\n");
		log("        only rewrite when the wide (high) part width is >= N (default 8).\n");
		log("\n");
		log("    -margin F\n");
		log("        require narrow_arrival > wide_arrival + F (default 0.0).\n");
		log("\n");
		log("    -hier-arrival\n");
		log("        seed each module's input port arrivals from its parent instead of\n");
		log("        charging every port zero. Without this a late operand that reaches\n");
		log("        the adder through a port -- the carry between two slices of a wide\n");
		log("        counter, say -- is indistinguishable from a register output, and no\n");
		log("        such adder is ever rewritten. Costs a few extra arrival walks per\n");
		log("        module, over the whole design rather than the selection. Off by\n");
		log("        default.\n");
		log("\n");
		log("    -hier-rounds N\n");
		log("        cap the instance-chain fixpoint at N rounds (default 8). A chain\n");
		log("        deeper than N keeps under-estimated arrivals, so it loses rewrites\n");
		log("        rather than gaining wrong ones.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing OPT_CARRY_SELECT pass (late-operand carry-select).\n");

		int max_narrow = 16;
		int min_wide = 8;
		double margin = 0.0;
		bool hier_arrival = false;
		int hier_rounds = 8;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-max-narrow" && argidx + 1 < args.size()) {
				max_narrow = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-min-wide" && argidx + 1 < args.size()) {
				min_wide = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-margin" && argidx + 1 < args.size()) {
				margin = atof(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-hier-arrival") {
				hier_arrival = true;
				continue;
			}
			if (args[argidx] == "-hier-rounds" && argidx + 1 < args.size()) {
				hier_rounds = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		// Both halves of the hierarchy walk run over the whole design, not the
		// selection: a port's arrival is a property of its parent, which may
		// well be outside the selection being rewritten.
		HierArrival internal, seeded;
		if (hier_arrival) {
			std::vector<Module *> bottom_up = modules_bottom_up(design);
			internal = measure_internal_depth(design, bottom_up, hier_rounds);
			seeded = seed_port_arrival(design, bottom_up, internal, hier_rounds);
		}

		int total = 0;
		for (auto module : design->selected_modules()) {
			OptCarrySelectWorker worker(module, max_narrow, min_wide, margin);
			dict<SigBit, double> instances;
			if (hier_arrival) {
				// Recover the same instance arrivals the seeding pass saw, so a
				// late operand produced inside this module by a child instance
				// is ranked the way the analysis ranked it.
				HierTiming timing(module, seeded.count(module) ? &seeded.at(module) : nullptr);
				timing.resolve_instances(design, internal, hier_rounds);
				instances = timing.inst_arrival;
				worker.port_arrival = seeded.count(module) ? &seeded.at(module) : nullptr;
				worker.inst_arrival = &instances;
			}
			worker.run();
			total += worker.converted;
		}
		log("Converted %d adder(s) to carry-select form.\n", total);
	}
} OptCarrySelectPass;

PRIVATE_NAMESPACE_END
