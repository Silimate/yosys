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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "passes/opt/rewrite_utils.h"

// opt_mux_odc: fold a mux select into its own data cone.
//
// A mux arm is only observable for one value of the select, so anything inside
// that arm's cone which the select already forces to a constant may be replaced
// by that constant. The shape this targets is a control signal that ORs in the
// very select that gates it:
//
//     wire hit  = valid | (fmt == A) | (fmt == B) | ...;   // valid forces hit
//     wire [1:0] res = hit ? f(x) : g(x);                  // deep cone
//     assign out = valid ? res : bypass;                   // arm gated by valid
//
// Under `valid` the OR is 1, so the whole `fmt` decode ahead of it is dead
// weight on the path -- but only along the arm, which is why plain constant
// propagation cannot do this. Folding it deletes the decode from the cone
// (usually shrinking area too, since the classifier disappears).
//
// Soundness. Replacing a candidate `c` by the constant `value` is free when the
// select equals `value`, because `c` already equals it there. The whole proof is
// therefore about the other case: under `select != value` nothing observable may
// depend on `c`. One forward walk from `c` decides that, propagating "this net
// may now differ" and refusing every way that difference could be seen:
//
//   1. Implication. The select must force the candidate structurally: an OR
//      whose inputs include the select (forced to 1 when the select is 1), or
//      the dual AND (forced to 0 when the select is 0). No SAT, no don't-care
//      guessing -- just the gate's own truth table. The shape also fixes which
//      select value, and so which mux arm, the fold is justified under.
//
//   2. Exclusivity. The walk stops at a mux on the same select that takes the
//      differing net only on the arm being specialized: under the other select
//      value that mux drives its other arm, so the difference goes no further.
//      Every other use propagates -- including the same mux's opposite arm,
//      which is walked through rather than rejected outright, since what lies
//      past it may well be gated too. A difference that reaches a module output
//      or a `keep` wire is rejected; one that reaches nothing observable is
//      harmless. At least one gated arm must be reached, so dead logic is left
//      to opt_clean instead of being "folded". This pass never duplicates a cone
//      to buy exclusivity, so a rewrite can only ever remove logic.
//
//   3. Combinational reach. Only combinational cells may be walked through. A
//      flip-flop or latch would capture the differing value during a cycle when
//      the arm is not selected and replay it on a later cycle when it is, which
//      the argument above does not cover: it only says the difference is
//      invisible *in the same instant*. A submodule instance counts as
//      combinational only if it, and everything it instantiates, is -- hierarchy
//      is common here since opt_boundary keeps it. Anything still holding logic
//      in a process is out of scope entirely: the index is built from cells, and
//      the walk needs a complete view of every driver and reader, so such
//      modules are skipped rather than analysed.
//
// The rewrite is an observability don't-care: gold and gate genuinely differ on
// internal nodes (that is the point), so `-strict` disables the pass for the
// formal flow, the same way opt_argmax's learned-table mode is gated.
//
// Cost. The pass runs on every design and folds on very few, so the search is
// arranged to touch each cell a bounded number of times and nothing more.
// Candidates are read straight out of the select's fanout rather than searched
// for in the arms; muxes are grouped by select, so a select driving a thousand
// muxes costs one search rather than a thousand; and the walk that proves
// exclusivity is the same walk that finds the arms, so the cone is never
// revisited to check the other condition. The verdict a walk reaches about a
// cell depends only on the cell and the select, never on which candidate the
// walk started from, so the verdicts are memoized for the whole select: where
// one enable qualifies thousands of gates that share a downstream cone -- the
// shape that made this pass run for hours on a real block -- that is the
// difference between linear and quadratic. Folds are batched into one rewrite
// per sweep, because re-indexing after each one was quadratic in the number of
// fold sites. What is left is charged against a single per-module budget --
// every loop that grows with the netlist, the per-sweep re-index included -- so
// an adversarial shape degrades into skipped candidates rather than a pass that
// does not finish.

struct OptMuxOdcWorker
{
	Module *module;
	SigMap sigmap;
	CellTypes &ct;
	// Keyed by module type and shared across the whole design: the answer
	// cannot change as the pass runs, since deleting cells only ever makes a
	// module more combinational.
	dict<IdString, bool> &comb_cache;

	// Index over the module, rebuilt at the top of every sweep. It deliberately
	// covers *all* cells, not just selected ones: the walk is only sound if it
	// can see every reader. Only the rewrite honours the selection.
	dict<SigBit, Cell *> driver; // filled by the shared indexer; unused here,
	                             // since the search only ever walks forward
	dict<SigBit, pool<Cell *>> consumers;
	pool<SigBit> escapes;  // module output ports and `keep` wires
	pool<Cell *> selected; // cells this invocation is allowed to touch

	int regions = 0;
	int cells_removed = 0;

	// One per-module work limit, shared across the sweeps in run(): a step is a
	// cell visited, a reader examined, a candidate tested, or -- from the second
	// sweep on, since the first index is unavoidable -- a cell re-indexed. Every
	// loop that can grow with the netlist charges it, so the pass cannot run
	// longer than the limit allows however the design is shaped. Memory needs no
	// separate limit: the memo, the DFS stack and the index are all bounded by
	// the module's own cell and pin counts. Running out skips the candidates
	// that are left, which can lose a fold but never change one.
	int64_t walk_budget = 20000000;
	int max_hier_depth = 16;
	int skipped = 0;
	int sweeps = 0;

	OptMuxOdcWorker(Module *module, CellTypes &ct, dict<IdString, bool> &comb_cache)
	    : module(module), ct(ct), comb_cache(comb_cache) {}

	// An empty fallback for dict::at() has to outlive the range-for that walks
	// it, since dict::at(key, defval) hands back a reference to defval.
	static const pool<Cell *> no_cells;

	void index()
	{
		sigmap.set(module);
		index_module_bits(module, sigmap, driver, consumers, escapes);
		selected.clear();
		for (auto cell : module->selected_cells())
			selected.insert(cell);
	}

	// Memoized: may the forward walk cross this cell type without leaving the
	// instant the select justified? Builtins are trusted to the cell table;
	// a submodule qualifies only if everything inside it does too.
	bool type_is_combinational(IdString type, int depth = 0)
	{
		auto it = comb_cache.find(type);
		if (it != comb_cache.end())
			return it->second;
		if (depth > max_hier_depth)
			return false;

		Module *sub = module->design->module(type);
		bool result;
		if (sub == nullptr)
			result = ct.cell_evaluable(type);
		else if (sub->get_blackbox_attribute())
			result = false; // contents unknown, so assume it can hold state
		else if (!sub->processes.empty())
			result = false; // a register may still be hiding in a process
		else {
			comb_cache[type] = false; // breaks recursive hierarchies
			result = true;
			for (auto sub_cell : sub->cells())
				if (!type_is_combinational(sub_cell->type, depth + 1)) {
					result = false;
					break;
				}
		}
		comb_cache[type] = result;
		return result;
	}

	// The select and arm currently being examined, and the muxes on that select
	// that read a given bit on the arm being specialized and on its opposite.
	// Set once per (select, arm); everything below is a function of these.
	SigBit sel;
	dict<SigBit, pool<Cell *>> arm_readers, other_readers;

	// What one cell contributes to a verdict: whether it is observed outright,
	// whether any of its own output bits already lands on a gated arm, and the
	// readers the walk has to continue through. The DFS below scans a cell once
	// to queue its readers and once more to combine their verdicts, and the two
	// visits have to agree on that reader set, so both go through here.
	struct CellScan {
		bool observed = false;
		bool reaches = false;
		std::vector<Cell *> readers;
	};
	CellScan scan;

	void scan_cell(Cell *cell)
	{
		scan.observed = false;
		scan.reaches = false;
		scan.readers.clear();
		for (auto &conn : cell->connections()) {
			if (!cell->output(conn.first))
				continue;
			for (auto bit : sigmap(conn.second)) {
				// A port or a `keep` wire is observed whatever the select does,
				// and reaching the select itself would mean the very condition
				// the fold rests on depends on the fold.
				if (escapes.count(bit) || bit == sel) {
					scan.observed = true;
					return;
				}
				for (auto reader : consumers.at(bit, no_cells)) {
					walk_budget--;
					// A mux on this select that takes the bit only on the arm
					// being specialized is driving its other arm under the
					// other select value, so the difference stops here.
					if (arm_readers.at(bit, no_cells).count(reader) &&
					    !other_readers.at(bit, no_cells).count(reader)) {
						scan.reaches = true;
						continue;
					}
					// A state element would hold the differing value past the
					// cycle whose select justified it -- see condition 3.
					if (!type_is_combinational(reader->type)) {
						scan.observed = true;
						return;
					}
					scan.readers.push_back(reader);
				}
			}
		}
	}

	// A cell's verdict under the current (select, arm): `gated` is conditions 2
	// and 3 together -- every way a difference at this cell could be observed is
	// a mux arm the select already gates -- and `reaches` says whether any arm
	// is reached at all, which is what separates a real fold from dead logic.
	//
	// Neither depends on which candidate started the walk, only on the cell and
	// the (select, arm) pair, so the verdicts are memoized for the whole select.
	// That is the difference between linear and quadratic where one enable
	// qualifies thousands of gates that share a downstream cone: without the
	// memo each of those candidates re-walks the same cells.
	struct Verdict { bool gated, reaches; };
	dict<Cell *, Verdict> memo;
	pool<Cell *> open; // cells on the current DFS path

	enum WalkResult { FOLDABLE, OBSERVED, OVER_BUDGET };

	WalkResult classify(Cell *start)
	{
		open.clear();
		std::vector<Cell *> stack = {start};
		while (!stack.empty()) {
			if (walk_budget <= 0)
				return OVER_BUDGET;
			walk_budget--;
			Cell *cell = stack.back();
			if (memo.count(cell)) {
				stack.pop_back();
				continue;
			}
			// First visit queues the readers and leaves the cell underneath
			// them; the second one finds their verdicts in and combines.
			bool expanding = open.insert(cell).second;
			scan_cell(cell);
			if (!scan.observed && expanding) {
				bool pending = false;
				for (auto reader : scan.readers)
					if (!memo.count(reader) && !open.count(reader)) {
						stack.push_back(reader);
						pending = true;
					}
				if (pending)
					continue;
			}
			Verdict v{!scan.observed, scan.reaches};
			for (auto reader : scan.readers) {
				if (!v.gated)
					break;
				auto it = memo.find(reader);
				// Still open means a combinational loop closed back onto the
				// path, which the same-instant argument does not cover.
				if (it == memo.end() || !it->second.gated) {
					v = Verdict{false, false};
					break;
				}
				v.reaches |= it->second.reaches;
			}
			memo[cell] = v;
			open.erase(cell);
			stack.pop_back();
		}
		const Verdict &v = memo.at(start);
		return v.gated && v.reaches ? FOLDABLE : OBSERVED;
	}

	// Input bits that on their own decide the output, per the gate's truth table.
	// Being an input is not enough: a bitwise $or may have wide operands but a
	// 1-bit result, in which case only bit 0 of each operand is even read.
	void controlling_bits(Cell *cell, std::vector<SigBit> &out)
	{
		IdString type = cell->type;
		for (auto &conn : cell->connections()) {
			if (cell->output(conn.first))
				continue;
			SigSpec in = sigmap(conn.second);
			if (GetSize(in) == 0)
				continue;
			if (type.in(ID($or), ID($and), ID($_OR_), ID($_AND_)))
				out.push_back(in[0]);
			else if (type.in(ID($reduce_or), ID($reduce_and), ID($logic_or)))
				// Any one bit settles an OR/AND reduction or a nonzero test.
				for (auto bit : in)
					out.push_back(bit);
			else if (type == ID($logic_and))
				// Needs a whole operand to be zero, so only a 1-bit one counts.
				if (GetSize(in) == 1)
					out.push_back(in[0]);
		}
	}

	// The gate's own truth table must force the output, given `sel` at `value`.
	bool forces_output(Cell *cell, bool value)
	{
		IdString type = cell->type;
		bool or_shaped = type.in(ID($or), ID($_OR_), ID($reduce_or), ID($logic_or));
		bool and_shaped = type.in(ID($and), ID($_AND_), ID($reduce_and), ID($logic_and));
		if (!(or_shaped || and_shaped))
			return false;
		// An OR pins high on a 1 input; an AND pins low on a 0 input.
		if (value != or_shaped)
			return false;
		// Restrict to single-bit results so the whole output can be replaced;
		// forcing one bit of a wide bitwise op would need the cell split first.
		if (!cell->hasPort(ID::Y) || GetSize(sigmap(cell->getPort(ID::Y))) != 1)
			return false;
		// The rewrite deletes the cell, which is exactly what `keep` forbids.
		if (cell->get_bool_attribute(ID::keep))
			return false;
		std::vector<SigBit> ctrl;
		controlling_bits(cell, ctrl);
		for (auto bit : ctrl)
			if (bit == sel)
				return true;
		return false;
	}

	// One pass over the module: decide every fold against an unmutated index,
	// then apply them together. A fold only deletes a gate and ties its output
	// to a constant, so it can neither add a reader nor open a path that
	// another fold's walk relied on being absent, and a fold it starves of
	// readers merely becomes dead logic. Returns the number of folds applied.
	int sweep()
	{
		// Rebuilding the index is what a pathological number of sweeps would
		// multiply, so charge every sweep but the first, whose index any pass
		// would have to pay for anyway.
		if (sweeps++)
			walk_budget -= GetSize(module->cells());
		index();

		// Muxes with a single-bit wire select, grouped by that select. Grouping
		// lets one candidate search and one set of verdicts serve every mux the
		// select drives, rather than repeating both per mux.
		dict<SigBit, std::vector<Cell *>> muxes_by_sel;
		for (auto cell : module->selected_cells()) {
			if (!cell->type.in(ID($mux), ID($_MUX_)))
				continue;
			SigSpec sel_sig = sigmap(cell->getPort(ID::S));
			if (GetSize(sel_sig) == 1 && sel_sig[0].is_wire())
				muxes_by_sel[sel_sig[0]].push_back(cell);
		}

		dict<Cell *, bool> folds;
		for (auto &sel_muxes : muxes_by_sel) {
			sel = sel_muxes.first;

			// $mux drives B when S is 1 and A when S is 0.
			for (int arm = 0; arm < 2; arm++) {
				IdString arm_port = arm ? ID::B : ID::A;
				IdString other_port = arm ? ID::A : ID::B;
				bool value = arm != 0;

				// A cell can only be forced by the select if the select is one
				// of its own inputs, so the candidates come straight off the
				// index -- and if there are none, the arm costs nothing.
				std::vector<Cell *> candidates;
				for (auto cand : consumers.at(sel, no_cells)) {
					walk_budget--;
					// The walk spans the whole module, so a partial selection
					// must not have its unselected cells rewritten.
					if (selected.count(cand) && !folds.count(cand) &&
					    forces_output(cand, value))
						candidates.push_back(cand);
				}
				if (candidates.empty() || walk_budget <= 0)
					continue;

				arm_readers.clear();
				other_readers.clear();
				for (auto mux : sel_muxes.second) {
					for (auto bit : sigmap(mux->getPort(arm_port))) {
						walk_budget--;
						arm_readers[bit].insert(mux);
					}
					for (auto bit : sigmap(mux->getPort(other_port))) {
						walk_budget--;
						other_readers[bit].insert(mux);
					}
				}
				memo.clear();

				for (auto cand : candidates) {
					WalkResult res = classify(cand);
					if (res == OVER_BUDGET) {
						skipped++;
						continue;
					}
					if (res != FOLDABLE)
						continue;
					log("  %s: forcing %s (%s) to %d under select %s\n",
					    log_id(module), log_id(cand), log_id(cand->type),
					    value ? 1 : 0, log_signal(sel));
					folds[cand] = value;
				}
			}
		}
		memo.clear();
		open.clear();

		for (auto &fold : folds) {
			SigSpec y = sigmap(fold.first->getPort(ID::Y));
			// Drop the driver first; the wire is then free to take the constant
			// that the select already implies along its arm.
			module->remove(fold.first);
			module->connect(y, fold.second ? State::S1 : State::S0);
			regions++;
			cells_removed++;
		}
		return GetSize(folds);
	}

	void run()
	{
		// A sweep's rewrite invalidates the index, and deleting a cell can make
		// a neighbour's cone exclusive that was not before, so sweep until one
		// comes up empty. Each sweep removes at least one cell, so this
		// terminates; in practice the second sweep is the one that finds
		// nothing. A budget that ran out mid-sweep would only make the next one
		// re-walk what it already skipped, so stop there instead.
		while (sweep() && walk_budget > 0) {}
	}
};

const pool<Cell *> OptMuxOdcWorker::no_cells;

struct OptMuxOdcPass : public Pass {
	OptMuxOdcPass() : Pass("opt_mux_odc", "fold a mux select into its own data cone") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_mux_odc [options] [selection]\n");
		log("\n");
		log("Fold a mux select into the cone of its own data arm. A mux arm only matters\n");
		log("for one value of the select, so a signal that the select structurally forces\n");
		log("to a constant -- an OR that takes the select as an input, or the dual AND --\n");
		log("can be replaced by that constant along the arm. This deletes control logic\n");
		log("(typically a decode or classifier) that is redundant once the select is known.\n");
		log("\n");
		log("The fold is only applied when everything reachable from the forced signal is\n");
		log("either unobservable or gated by that same select, so the pass never duplicates\n");
		log("logic and can only shrink the design.\n");
		log("\n");
		log("    -strict\n");
		log("        disable the rewrite. It is an observability don't-care, so gold and\n");
		log("        gate diverge on internal nodes and a node-matching equivalence check\n");
		log("        cannot confirm it.\n");
		log("\n");
		log("    -walk-budget N\n");
		log("        per-module work limit for the search (default 20000000). Candidates\n");
		log("        left over when it runs out are skipped, which can lose a fold but\n");
		log("        never change one.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_MUX_ODC pass (fold mux select into its data cone).\n");

		bool strict = false;
		int64_t walk_budget = -1;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-strict") {
				strict = true;
				continue;
			}
			if ((args[argidx] == "-walk-budget" || args[argidx] == "-walk_budget") &&
			    argidx + 1 < args.size()) {
				walk_budget = std::stoll(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_regions = 0, total_removed = 0;
		if (!strict) {
			// Both outlive the per-module workers: the cell table is a function
			// of the design, and a module type's combinationality never changes
			// as the pass runs, so rebuilding either per module was pure cost.
			CellTypes ct;
			ct.setup(design);
			dict<IdString, bool> comb_cache;

			for (auto module : design->selected_modules()) {
				// The index is built from cells, so logic still held in a
				// process is invisible to it -- and the walk is only sound with
				// a complete view of every driver and reader.
				if (!module->processes.empty()) {
					log("Skipping module %s because it contains processes "
					    "(run proc first).\n", log_id(module));
					continue;
				}
				OptMuxOdcWorker worker(module, ct, comb_cache);
				if (walk_budget > 0)
					worker.walk_budget = walk_budget;
				worker.run();
				total_regions += worker.regions;
				total_removed += worker.cells_removed;
				// One visible note per module, so a QoR change caused by a
				// truncated search is diagnosable from the log.
				if (worker.skipped)
					log_debug("Note: opt_mux_odc search limit reached in module %s; "
					          "%d candidate(s) skipped. Raise -walk-budget if QoR "
					          "matters more than runtime here.\n",
					          log_id(module), worker.skipped);
			}
		}

		log("Rewrote %d mux observability region(s); removed %d cell(s).\n",
		    total_regions, total_removed);

		if (total_regions)
			Yosys::run_pass("opt_expr -full");
	}
} OptMuxOdcPass;

PRIVATE_NAMESPACE_END
