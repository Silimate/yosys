/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *                2026  Akash Levy        <akash@silimate.com>
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

#include "kernel/celltypes.h"
#include "kernel/sigtools.h"
#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Shannon-expand a deep combinational cone on a narrow, late-arriving select.
//
// Control state -- a mode register, a format code -- lands at the end of a cycle
// and then has a whole decode chain ahead of it before the data path it steers
// even starts. Every other input to that decode is available much earlier, so
// the decode can be run once per value of the select off those early inputs and
// the select left only to pick between the answers:
//
//   f(sel, x)  ===>  bmux_sel( f(0, x), f(1, x), ..., f(2^b-1, x) )
//
// which replaces the select's whole path through the cone with one mux.
//
// Correctness needs nothing of the cone but that it be combinational. Copy v is
// selected exactly when sel == v, and every other input the copies share carries
// its true value, so pinning sel to v inside copy v cannot change what the
// selected copy computes -- even where a path from sel leaves the region and
// comes back, since that path also carries its sel == v value.
//
// What it does need care over is *where* to stop. Expanding further always
// shortens the select's path more, and always costs another 2^b-1 copies of
// everything added, so the boundary is chosen by what the copies buy on the path
// (see region_gain) rather than by how deep the cone can be followed.
struct ShannonWorker {
	Module *module;
	SigMap sigmap;
	CellTypes ct;

	// Tunables (see Pass::execute).
	int max_sel_bits = 3;
	int max_cut_bits = 64;
	int max_dup_cells = 2048;
	int max_region_cells = 1024;
	int min_gain = 2;

	int expanded = 0;
	int cells_added = 0;

	dict<SigBit, Cell *> bit_to_driver;
	dict<SigBit, pool<Cell *>> bit_to_readers;
	pool<SigBit> visible_bits;  // read from outside the module's cell graph

	// dict::at(key, default) hands back a reference to the default, so a literal
	// {} there dangles the moment the call expression ends -- fatal to walk.
	const pool<Cell *> no_readers;

	const pool<Cell *> &readers(const SigBit &bit) const
	{
		return bit_to_readers.at(bit, no_readers);
	}

	ShannonWorker(Module *module) : module(module), sigmap(module)
	{
		ct.setup_internals();
		ct.setup_internals_mem();
		ct.setup_stdcells();
		ct.setup_stdcells_mem();
		build_index();
	}

	void build_index()
	{
		bit_to_driver.clear();
		bit_to_readers.clear();
		visible_bits.clear();
		level_memo.clear();

		for (auto cell : module->cells())
			for (auto &conn : cell->connections())
				for (auto bit : sigmap(conn.second)) {
					if (bit.wire == nullptr)
						continue;
					if (cell->output(conn.first))
						bit_to_driver[bit] = cell;
					else
						bit_to_readers[bit].insert(cell);
				}

		// Read by something the cell graph cannot see, so it pins whatever drives
		// it. Module assignments need no scan of their own: sigmap already
		// collapses an alias onto one bit, so a reader of either name is a reader
		// of that bit, and an aliased port output is caught right here.
		for (auto wire : module->wires())
			if (wire->port_output || wire->get_bool_attribute(ID::keep))
				for (auto bit : sigmap(SigSpec(wire)))
					visible_bits.insert(bit);
	}

	// A cell whose outputs are state, so the forward walk stops in front of it
	// and the select's own driver qualifies as late.
	static bool is_ff(Cell *cell) { return StaticCellTypes::categories.is_ff(cell->type); }

	// Safe to duplicate: known, purely combinational semantics. Anything with
	// state, a side effect or an unknown body is out -- a second copy of a memory
	// port or a $print is not the same circuit.
	bool can_copy(Cell *cell) const
	{
		return ct.cell_evaluable(cell->type) && !is_ff(cell) &&
		       !cell->get_bool_attribute(ID::keep);
	}

	// ------------------------------------------------------------- arrival

	// Longest combinational level of a bit, counting from flops and inputs.
	// Iterative, and a back edge counts as level 0: a vectorizing frontend leaves
	// cell-level loops that are perfectly acyclic bit by bit.
	dict<SigBit, int> level_memo;
	int bit_level(const SigBit &root_bit)
	{
		if (root_bit.wire == nullptr)
			return 0;
		if (level_memo.count(root_bit))
			return level_memo.at(root_bit);

		vector<std::pair<SigBit, bool>> stack;
		pool<SigBit> on_stack;
		stack.push_back({root_bit, false});
		while (!stack.empty()) {
			SigBit bit = stack.back().first;
			bool expanded_now = stack.back().second;
			Cell *drv = bit.wire ? bit_to_driver.at(bit, nullptr) : nullptr;
			if (level_memo.count(bit) || drv == nullptr || is_ff(drv)) {
				if (!level_memo.count(bit))
					level_memo[bit] = 0;
				on_stack.erase(bit);
				stack.pop_back();
				continue;
			}
			if (!expanded_now) {
				stack.back().second = true;
				on_stack.insert(bit);
				for (auto &conn : drv->connections())
					if (drv->input(conn.first))
						for (auto b : sigmap(conn.second))
							if (b.wire && !level_memo.count(b) &&
							    !on_stack.count(b))
								stack.push_back({b, false});
				continue;
			}
			int worst = 0;
			for (auto &conn : drv->connections())
				if (drv->input(conn.first))
					for (auto b : sigmap(conn.second))
						if (b.wire)
							worst = std::max(worst, level_memo.at(b, 0));
			level_memo[bit] = worst + 1;
			on_stack.erase(bit);
			stack.pop_back();
		}
		return level_memo.at(root_bit, 0);
	}

	int sig_level(const SigSpec &sig)
	{
		int worst = 0;
		for (auto bit : sigmap(sig))
			worst = std::max(worst, bit_level(bit));
		return worst;
	}

	// ------------------------------------------------------------- regions

	// One candidate boundary: the cells to copy, the bits to mux, and what the
	// copies would buy.
	struct Region {
		pool<Cell *> cells;
		SigSpec cut;
		int gain = 0;
		int before = 0;
		int after = 0;
	};

	// Bits `cells` drive that anything outside `cells` reads.
	void region_cut(const pool<Cell *> &cells, SigSpec &cut)
	{
		pool<SigBit> seen;
		for (auto cell : cells)
			for (auto &conn : cell->connections()) {
				if (!cell->output(conn.first))
					continue;
				for (auto bit : sigmap(conn.second)) {
					if (bit.wire == nullptr || !seen.insert(bit).second)
						continue;
					bool outside = visible_bits.count(bit) != 0;
					for (auto rd : readers(bit))
						if (!cells.count(rd))
							outside = true;
					if (outside)
						cut.append(bit);
				}
			}
	}

	// Level of the cut once the copies have pinned `sel` to a constant.
	//
	// A cell inside the region whose whole cone within the region reaches only
	// `sel` folds away entirely -- that is the decode the expansion is aimed at.
	// A cell that also reads something from outside does not, and is priced at
	// its full depth: constant-folding may still simplify it, and pricing that
	// optimistically would talk the pass into expansions that do not pay.
	int folded_level(const pool<Cell *> &cells, const pool<SigBit> &sel_bits,
	                 const SigSpec &cut)
	{
		dict<SigBit, int> lvl;
		dict<SigBit, bool> sel_only;

		// Region cells in topological order, so a cell's inputs are settled
		// before it. A back edge leaves a cell unsettled; it is priced from
		// whatever its settled inputs gave, matching bit_level's own rule.
		vector<Cell *> order;
		pool<Cell *> placed;
		for (bool grew = true; grew && GetSize(placed) < GetSize(cells);) {
			grew = false;
			for (auto cell : cells) {
				if (placed.count(cell))
					continue;
				bool ready = true;
				for (auto &conn : cell->connections()) {
					if (!cell->input(conn.first))
						continue;
					for (auto bit : sigmap(conn.second)) {
						Cell *drv = bit.wire ? bit_to_driver.at(bit, nullptr)
						                     : nullptr;
						if (drv != nullptr && cells.count(drv) &&
						    !placed.count(drv))
							ready = false;
					}
				}
				if (ready) {
					order.push_back(cell);
					placed.insert(cell);
					grew = true;
				}
			}
		}

		for (auto cell : order) {
			int worst = 0;
			bool only = true;
			for (auto &conn : cell->connections()) {
				if (!cell->input(conn.first))
					continue;
				for (auto bit : sigmap(conn.second)) {
					if (bit.wire == nullptr)
						continue;  // a constant folds either way
					if (sel_bits.count(bit))
						continue;  // pinned by the copy
					Cell *drv = bit_to_driver.at(bit, nullptr);
					if (drv != nullptr && cells.count(drv)) {
						if (!sel_only.at(bit, true))
							only = false;
						worst = std::max(worst, lvl.at(bit, 0));
					} else {
						only = false;
						worst = std::max(worst, bit_level(bit));
					}
				}
			}
			for (auto &conn : cell->connections()) {
				if (!cell->output(conn.first))
					continue;
				for (auto bit : sigmap(conn.second))
					if (bit.wire != nullptr) {
						sel_only[bit] = only;
						lvl[bit] = only ? 0 : worst + 1;
					}
			}
		}

		int worst = 0;
		for (auto bit : cut)
			worst = std::max(worst, lvl.at(bit, bit_level(bit)));
		return worst;
	}

	// What expanding to this boundary buys on the path: the cut stops waiting for
	// the select's trip through the cone and waits instead for the deepest copy,
	// or for the select plus the mux tree, whichever lands later.
	void region_gain(Region &r, const SigSpec &sel, const pool<SigBit> &sel_bits)
	{
		r.before = sig_level(r.cut);
		int mux_levels = GetSize(sel);
		r.after = std::max(folded_level(r.cells, sel_bits, r.cut),
		                   sig_level(sel) + mux_levels);
		r.gain = r.before - r.after;
	}

	// Grow the forward cone of `sel` a level at a time, and keep the boundary
	// whose copies buy the most. Deeper always shortens the select's path
	// further and always costs another 2^b-1 copies of everything added, so the
	// caps are what stop the walk and the gain is what picks among what it saw.
	bool best_region(const SigSpec &sel, Region &best)
	{
		pool<SigBit> sel_bits;
		for (auto bit : sigmap(sel))
			sel_bits.insert(bit);
		int copies = 1 << GetSize(sel);

		pool<Cell *> cells;
		pool<Cell *> frontier;
		for (auto bit : sel_bits)
			for (auto rd : readers(bit))
				frontier.insert(rd);

		bool found = false;
		while (!frontier.empty()) {
			pool<Cell *> next;
			for (auto cell : frontier) {
				if (cells.count(cell))
					continue;
				if (!can_copy(cell))
					return found;  // cannot copy it, so cannot pass it
				cells.insert(cell);
				if (GetSize(cells) > max_region_cells)
					return found;
				for (auto &conn : cell->connections())
					if (cell->output(conn.first))
						for (auto bit : sigmap(conn.second))
							if (bit.wire != nullptr)
								for (auto rd : readers(bit))
									if (!cells.count(rd) &&
									    !is_ff(rd))
										next.insert(rd);
			}
			if ((copies - 1) * GetSize(cells) > max_dup_cells)
				return found;

			Region r;
			r.cells = cells;
			region_cut(cells, r.cut);
			if (GetSize(r.cut) > max_cut_bits)
				return found;
			region_gain(r, sel, sel_bits);
			log_debug("    boundary %d cell(s), %d cut bit(s): %d -> %d level(s)\n",
			          GetSize(cells), GetSize(r.cut), r.before, r.after);
			if (r.gain >= min_gain && (!found || r.gain > best.gain)) {
				best = r;
				found = true;
			}
			frontier.swap(next);
		}
		return found;
	}

	// ------------------------------------------------------------- rewrite

	void expand(const SigSpec &sel, Region &r)
	{
		int copies = 1 << GetSize(sel);
		vector<dict<SigBit, SigBit>> remap(copies);

		for (int v = 0; v < copies; v++) {
			// The copy's own view of the select, and a fresh wire for every bit
			// the region drives. Populated before any cell is cloned so the
			// clones need no ordering.
			for (int i = 0; i < GetSize(sel); i++)
				remap[v][sigmap(sel)[i]] =
				    SigBit((v >> i) & 1 ? State::S1 : State::S0);
			for (auto cell : r.cells)
				for (auto &conn : cell->connections()) {
					if (!cell->output(conn.first))
						continue;
					for (auto bit : sigmap(conn.second))
						if (bit.wire != nullptr && !remap[v].count(bit))
							remap[v][bit] =
							    SigBit(module->addWire(NEW_ID));
				}

			for (auto cell : r.cells) {
				Cell *copy = module->addCell(NEW_ID, cell);
				for (auto &conn : cell->connections()) {
					SigSpec mapped;
					for (auto bit : conn.second) {
						SigBit sb = sigmap(bit);
						mapped.append(remap[v].at(sb, bit));
					}
					copy->setPort(conn.first, mapped);
				}
				cells_added++;
			}
		}

		// One table read over the whole cut: the copies are laid out select-major,
		// which is the order $bmux indexes them in.
		SigSpec data;
		for (int v = 0; v < copies; v++)
			for (auto bit : r.cut)
				data.append(remap[v].at(bit));
		SigSpec picked = module->Bmux(NEW_ID, data, sel);
		cells_added++;

		// The originals are what the cut used to be driven by, and every reader
		// of theirs inside the region now reads a copy instead.
		for (auto cell : r.cells)
			module->remove(cell);
		module->connect(r.cut, picked);
		expanded++;
	}

	// Selects worth trying: the outputs of one flop, narrow enough that 2^b
	// copies is a price worth considering.
	void collect_selects(vector<SigSpec> &sels)
	{
		pool<SigSpec> seen;
		for (auto cell : module->selected_cells()) {
			if (!is_ff(cell) || !cell->hasPort(ID::Q))
				continue;
			SigSpec q = sigmap(cell->getPort(ID::Q));
			if (GetSize(q) < 1 || GetSize(q) > max_sel_bits)
				continue;
			// A repeated or constant bit is not a select of its own width.
			pool<SigBit> uniq;
			bool ok = true;
			for (auto bit : q)
				if (bit.wire == nullptr || !uniq.insert(bit).second)
					ok = false;
			if (ok && seen.insert(q).second)
				sels.push_back(q);
		}
	}

	bool run_once()
	{
		vector<SigSpec> sels;
		collect_selects(sels);
		log_debug("opt_shannon: %d select candidate(s) in %s\n", GetSize(sels),
		          log_id(module));

		SigSpec best_sel;
		Region best;
		bool found = false;
		for (auto &sel : sels) {
			Region r;
			if (!best_region(sel, r))
				continue;
			log_debug("  %s: %d cell(s) x %d, %d cut bit(s), %d level(s) saved\n",
			          log_signal(sel), GetSize(r.cells), 1 << GetSize(sel),
			          GetSize(r.cut), r.gain);
			if (!found || r.gain > best.gain) {
				best = r;
				best_sel = sel;
				found = true;
			}
		}
		if (!found)
			return false;

		log("  expanding %s (%d bit(s)) over %d cell(s), %d cut bit(s): %d -> %d "
		    "level(s)\n",
		    log_signal(best_sel), GetSize(best_sel), GetSize(best.cells),
		    GetSize(best.cut), best.before, best.after);
		expand(best_sel, best);
		return true;
	}

	void run(int max_rounds)
	{
		for (int round = 0; round < max_rounds; round++) {
			if (!run_once())
				break;
			// The rewrite rewires the cone, so every index and every level is
			// stale before the next candidate is weighed.
			sigmap.set(module);
			build_index();
		}
	}
};

struct OptShannonPass : public Pass {
	OptShannonPass() : Pass("opt_shannon", "Shannon-expand a cone on a late narrow select") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_shannon [options] [selection]\n");
		log("\n");
		log("Shannon-expand a deep combinational cone on a narrow, late-arriving\n");
		log("select:\n");
		log("\n");
		log("    f(sel, x)  ===>  bmux_sel( f(0, x), f(1, x), ..., f(2^b-1, x) )\n");
		log("\n");
		log("Control state -- a mode register, a format code -- lands at the end of a\n");
		log("cycle and then has a whole decode chain ahead of it before the data path\n");
		log("it steers even starts. The other inputs to that decode arrive much\n");
		log("earlier, so the decode is run once per value of the select off those, and\n");
		log("the select is left only to pick between the answers: its whole path\n");
		log("through the cone becomes one mux.\n");
		log("\n");
		log("The cost is 2^b-1 extra copies of the cone, so the boundary the copies\n");
		log("stop at is chosen by what they buy on the path -- the levels the cut\n");
		log("stops waiting for -- rather than by how deep the cone can be followed.\n");
		log("A sub-cone that reads only the select folds to a constant in every copy\n");
		log("and is what the expansion is really aimed at; a cell that also reads\n");
		log("something earlier is priced at its full depth.\n");
		log("\n");
		log("    -max-sel-bits N\n");
		log("        widest select to expand on (default 3), so at most 2^N copies.\n");
		log("\n");
		log("    -max-cut-bits N\n");
		log("        widest boundary to mux (default 64).\n");
		log("\n");
		log("    -max-dup-cells N\n");
		log("        most cells one expansion may add in copies (default 2048).\n");
		log("\n");
		log("    -max-region-cells N\n");
		log("        largest cone to consider expanding (default 1024).\n");
		log("\n");
		log("    -min-gain N\n");
		log("        levels an expansion has to save to fire (default 2).\n");
		log("\n");
		log("    -max-rounds N\n");
		log("        most expansions per module (default 4).\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_SHANNON pass (Shannon-expand a cone on a late "
		                   "narrow select).\n");
		int max_sel_bits = 3, max_cut_bits = 64, max_dup_cells = 2048;
		int max_region_cells = 1024, min_gain = 2, max_rounds = 4;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if ((args[argidx] == "-max-sel-bits" || args[argidx] == "-max_sel_bits") &&
			    argidx + 1 < args.size()) {
				max_sel_bits = std::stoi(args[++argidx]);
				// 2^N copies are laid out in one $bmux table, and the walk
				// counts them in an int.
				if (max_sel_bits < 1 || max_sel_bits > 8)
					log_cmd_error("-max-sel-bits must be in 1..8\n");
				continue;
			}
			if ((args[argidx] == "-max-cut-bits" || args[argidx] == "-max_cut_bits") &&
			    argidx + 1 < args.size()) {
				max_cut_bits = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-dup-cells" || args[argidx] == "-max_dup_cells") &&
			    argidx + 1 < args.size()) {
				max_dup_cells = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-region-cells" ||
			     args[argidx] == "-max_region_cells") &&
			    argidx + 1 < args.size()) {
				max_region_cells = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-min-gain" || args[argidx] == "-min_gain") &&
			    argidx + 1 < args.size()) {
				min_gain = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-rounds" || args[argidx] == "-max_rounds") &&
			    argidx + 1 < args.size()) {
				max_rounds = std::stoi(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_expanded = 0, total_cells = 0;
		for (auto module : design->selected_modules()) {
			if (module->has_processes_warn())
				continue;
			ShannonWorker worker(module);
			worker.max_sel_bits = max_sel_bits;
			worker.max_cut_bits = max_cut_bits;
			worker.max_dup_cells = max_dup_cells;
			worker.max_region_cells = max_region_cells;
			worker.min_gain = min_gain;
			worker.run(max_rounds);
			total_expanded += worker.expanded;
			total_cells += worker.cells_added;
		}

		log("Shannon-expanded %d cone(s); emitted %d new cell(s).\n", total_expanded,
		    total_cells);
		if (total_expanded > 0)
			Yosys::run_pass("clean -purge");
	}
} OptShannonPass;

PRIVATE_NAMESPACE_END
