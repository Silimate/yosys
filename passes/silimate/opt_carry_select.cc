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
#include <memory>
#include <utility>
#include <vector>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "passes/silimate/unit_delay.h"

// Marks the incrementer/mux a carry-select rewrite emits so peepopt -muxorder
// (which would otherwise fold `s ? (a+1) : a` back into `a + s`, putting the
// late select on a wide ripple carry) leaves them alone.
static const IdString kAttrCarrySelect = ID(carry_select);

// Absolute arrival of a bit, resolved across module boundaries on demand.
//
// The pass ranks operands with a module-local walk, and that walk credits any
// bit it has no driver for with arrival 0 -- a constant, but also an input port
// or a child instance output, since an instance is an unknown cell type and so
// already ends a path. A late operand reaching an adder through a port is
// therefore indistinguishable from a register output.
//
// Answers are memoized per (module, bit) rather than summarized per module: a
// summary has to charge every output the latest of *all* the module's inputs,
// which inflates outputs the late input cannot even reach, and over-estimating
// the narrow operand is exactly what authorizes an unprofitable rewrite. Asking
// at the moment a site is ranked also means there is no precomputed state for a
// rewrite elsewhere to leave stale.
struct HierArrivalQuery {
	Design *design;

	// Per-module walk, built on first use. Each owns its own sigmap and driver
	// map, and reaches back here for the bits it has no driver for.
	dict<Module *, FracDelayTiming *> timing;
	// Who instantiates a module, and through which cell. Structural, so a
	// conversion (which only adds $add/$mux cells) cannot invalidate it.
	dict<Module *, std::vector<std::pair<Module *, Cell *>>> parents;

	dict<Module *, dict<SigBit, double>> memo;
	// Recursion guard. A hierarchy or combinational cycle charges its back edge
	// 0, which under-estimates and so loses rewrites rather than inventing them.
	dict<Module *, pool<SigBit>> active;

	HierArrivalQuery(Design *design) : design(design)
	{
		for (auto module : design->modules())
			for (auto cell : module->cells())
				if (Module *child = design->module(cell->type))
					parents[child].push_back(std::make_pair(module, cell));
	}

	~HierArrivalQuery()
	{
		for (auto &entry : timing)
			delete entry.second;
	}

	// Conversions change the depth of the module they land in, so anything
	// answered by reading through that module has to be asked again.
	void invalidate()
	{
		for (auto &entry : timing)
			delete entry.second;
		timing.clear();
		memo.clear();
	}

	FracDelayTiming *walk(Module *module);

	double arrival(Module *module, SigBit bit)
	{
		FracDelayTiming *t = walk(module);
		bit = t->sigmap(bit);

		auto hit = memo.find(module);
		if (hit != memo.end()) {
			auto bit_hit = hit->second.find(bit);
			if (bit_hit != hit->second.end())
				return bit_hit->second;
		}
		if (active[module].count(bit))
			return 0;

		active[module].insert(bit);
		// driver_of() already returns null for ports, constants, registers and
		// instances, so a non-null driver is in-module logic this walk can cost.
		RTLIL::Cell *drv = t->driver_of(bit);
		double result = drv != nullptr ? t->arrival_of(drv) : boundary_arrival(module, bit);
		active[module].erase(bit);

		memo[module][bit] = result;
		return result;
	}

	// A bit the module's own walk cannot cost: a child instance drives it, it is
	// an input port, or it is a constant or register output.
	double boundary_arrival(Module *module, SigBit bit)
	{
		FracDelayTiming *t = walk(module);

		// Instance output: charge what is actually inside the child, by asking
		// for the matching output port bit in the child's own coordinates.
		auto drv = t->driver_map.find(bit);
		if (drv != t->driver_map.end()) {
			Cell *cell = drv->second;
			Module *child = design->module(cell->type);
			if (child != nullptr) {
				for (auto &conn : cell->connections()) {
					if (!cell->output(conn.first))
						continue;
					Wire *child_port = child->wire(conn.first);
					if (child_port == nullptr)
						continue;
					SigSpec parent_bits = t->sigmap(conn.second);
					SigSpec child_bits = SigSpec(child_port);
					for (int i = 0; i < GetSize(parent_bits) && i < GetSize(child_bits); i++)
						if (parent_bits[i] == bit)
							return arrival(child, child_bits[i]);
				}
			}
			return 0; // register output or a cell type nothing can see through
		}

		if (bit.wire == nullptr || !bit.wire->port_input)
			return 0; // constant, or an undriven internal wire

		// Input port: the earliest arrival any instantiation gives it, so a
		// module is never rewritten on the strength of one favourable parent.
		// A parent that leaves the port unconnected or short supplies 0.
		auto instantiations = parents.find(module);
		if (instantiations == parents.end() || instantiations->second.empty())
			return 0; // top, or otherwise uninstantiated
		double earliest = -1.0;
		for (auto &parent : instantiations->second) {
			double here = 0;
			if (parent.second->hasPort(bit.wire->name)) {
				SigSpec conn = walk(parent.first)->sigmap(
					parent.second->getPort(bit.wire->name));
				if (bit.offset < GetSize(conn))
					here = arrival(parent.first, conn[bit.offset]);
			}
			earliest = earliest < 0 ? here : std::min(earliest, here);
		}
		return earliest < 0 ? 0 : earliest;
	}
};

// Walk that defers its boundary bits to the query that owns it.
struct QueryTiming : FracDelayTiming {
	HierArrivalQuery *query;
	Module *owner;

	QueryTiming(Module *module, HierArrivalQuery *query)
		: FracDelayTiming(module), query(query), owner(module)
	{
		build_connectivity();
	}

	double start_arrival(SigBit bit) override { return query->boundary_arrival(owner, bit); }
};

FracDelayTiming *HierArrivalQuery::walk(Module *module)
{
	auto hit = timing.find(module);
	if (hit != timing.end())
		return hit->second;
	FracDelayTiming *t = new QueryTiming(module, this);
	timing[module] = t;
	return t;
}

struct OptCarrySelectWorker : FracDelayTiming {
	int max_narrow;
	int min_wide;
	double margin;
	// Set only under -hier-arrival; null leaves every boundary bit at 0, as before.
	HierArrivalQuery *hier = nullptr;

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

	// Ports and child instance outputs, asked for as the ranking needs them.
	double start_arrival(SigBit bit) override
	{
		return hier == nullptr ? 0 : hier->boundary_arrival(module, bit);
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
		log("        resolve operand arrivals across module boundaries instead of\n");
		log("        charging every input port and instance output zero. Without this a\n");
		log("        late operand that reaches the adder through a port -- the carry\n");
		log("        between two slices of a wide counter, say -- is indistinguishable\n");
		log("        from a register output, and no such adder is ever rewritten.\n");
		log("        Arrivals are resolved on demand for the operands of candidate\n");
		log("        adders, so the cost follows those cones rather than the design. A\n");
		log("        module instantiated more than once takes the earliest arrival any\n");
		log("        instantiation gives a port, and a hierarchy cycle charges its back\n");
		log("        edge zero, so both cases lose rewrites rather than invent them.\n");
		log("        Off by default.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing OPT_CARRY_SELECT pass (late-operand carry-select).\n");

		int max_narrow = 16;
		int min_wide = 8;
		double margin = 0.0;
		bool hier_arrival = false;

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
			break;
		}
		extra_args(args, argidx, design);

		// Spans the whole design, not the selection: a port's arrival is a
		// property of its parent, which may well sit outside the selection.
		std::unique_ptr<HierArrivalQuery> hier;
		if (hier_arrival)
			hier.reset(new HierArrivalQuery(design));

		int total = 0;
		for (auto module : design->selected_modules()) {
			OptCarrySelectWorker worker(module, max_narrow, min_wide, margin);
			worker.hier = hier.get();
			worker.run();
			total += worker.converted;
			// This module's depth just changed, so drop anything the query
			// answered by reading through it.
			if (worker.converted != 0 && hier)
				hier->invalidate();
		}
		log("Converted %d adder(s) to carry-select form.\n", total);
	}
} OptCarrySelectPass;

PRIVATE_NAMESPACE_END
