/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Silimate Inc.
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
#include "kernel/satgen.h"
#include <fstream>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Maximum depth for BFS exploration of input cone
static const int MAX_INPUT_DEPTH = 10;

struct SatClockgateWorker
{
	Module *module;
	SigMap sigmap;
	
	// Maps output signal bits to their driver cells
	dict<SigBit, Cell*> sig_to_driver;
	
	SatClockgateWorker(Module *module) : module(module), sigmap(module)
	{
		// Build driver map: for each signal bit, find which cell drives it
		for (auto cell : module->cells()) {
			for (auto &conn : cell->connections()) {
				if (cell->output(conn.first)) {
					for (auto bit : sigmap(conn.second))
						sig_to_driver[bit] = cell;
				}
			}
		}
	}

	// Get the set of input signals feeding into a given signal (one level back)
	pool<SigBit> get_input_signals(SigBit bit)
	{
		pool<SigBit> inputs;
		bit = sigmap(bit);
		
		if (!sig_to_driver.count(bit))
			return inputs; // Primary input or constant
		
		Cell *driver = sig_to_driver[bit];
		for (auto &conn : driver->connections()) {
			if (driver->input(conn.first)) {
				for (auto input_bit : sigmap(conn.second)) {
					if (input_bit.wire != nullptr)
						inputs.insert(input_bit);
				}
			}
		}
		return inputs;
	}

	// BFS to collect input cone up to a certain depth
	pool<SigBit> get_input_cone(SigSpec sig, int max_depth)
	{
		pool<SigBit> visited;
		pool<SigBit> frontier;
		
		for (auto bit : sigmap(sig))
			if (bit.wire != nullptr)
				frontier.insert(bit);
		
		for (int depth = 0; depth < max_depth && !frontier.empty(); depth++) {
			pool<SigBit> next_frontier;
			for (auto bit : frontier) {
				if (visited.count(bit))
					continue;
				visited.insert(bit);
				
				for (auto input_bit : get_input_signals(bit)) {
					if (!visited.count(input_bit))
						next_frontier.insert(input_bit);
				}
			}
			frontier = next_frontier;
		}
		
		return visited;
	}

	// Check if fixing the input_set to specific values makes D == Q always true
	// Returns true if input_set can serve as an enable (when all bits are 0, D == Q)
	bool input_set_is_enable(const pool<SigBit> &input_set, SigSpec sig_d, SigSpec sig_q)
	{
		if (input_set.empty())
			return false;

		ezSatPtr ez;
		SatGen satgen(ez.get(), &sigmap);
		
		// Import the logic cone for D
		for (auto cell : module->cells())
			satgen.importCell(cell);
		
		// Create SAT variables for D and Q
		std::vector<int> d_vec = satgen.importSigSpec(sig_d);
		std::vector<int> q_vec = satgen.importSigSpec(sig_q);
		
		// Assert: all signals in input_set are 0
		for (auto bit : input_set) {
			std::vector<int> bit_vec = satgen.importSigSpec(SigSpec(bit));
			if (!bit_vec.empty())
				ez->assume(ez->NOT(bit_vec[0]));
		}
		
		// Assert: D != Q (we want this to be UNSAT)
		std::vector<int> neq_bits;
		for (size_t i = 0; i < d_vec.size() && i < q_vec.size(); i++) {
			neq_bits.push_back(ez->XOR(d_vec[i], q_vec[i]));
		}
		ez->assume(ez->expression(ezSAT::OpOr, neq_bits));
		
		// If UNSAT, then input_set=0 guarantees D == Q
		bool sat = ez->solve();
		return !sat;
	}

	// Recursively determine the enable input set via BFS expansion
	bool determine_enable_recursive(pool<SigBit> &input_set, SigSpec sig_d, SigSpec sig_q, int depth)
	{
		if (depth > MAX_INPUT_DEPTH) {
			log_debug("  Max depth reached, giving up\n");
			return false;
		}

		// Check if current input set works as enable
		if (input_set_is_enable(input_set, sig_d, sig_q)) {
			log_debug("  Found enable at depth %d with %zu signals\n", depth, input_set.size());
			return true;
		}

		// Expand input set via BFS (one more level)
		pool<SigBit> new_inputs;
		for (auto bit : input_set) {
			for (auto input_bit : get_input_signals(bit)) {
				if (!input_set.count(input_bit))
					new_inputs.insert(input_bit);
			}
		}

		if (new_inputs.empty()) {
			log_debug("  No more inputs to explore at depth %d\n", depth);
			return false;
		}

		// Add new inputs and recurse
		for (auto bit : new_inputs)
			input_set.insert(bit);

		return determine_enable_recursive(input_set, sig_d, sig_q, depth + 1);
	}

	// Create CE logic based on the input set and modify the FF
	// The enable condition is: when all input_set bits are 0, D == Q (hold)
	// So CE should be: OR of all input_set bits (active high: CE=1 means update)
	void create_ce_logic(const pool<SigBit> &input_set, FfData &ff)
	{
		if (input_set.empty())
			return;

		log("  Creating CE from %zu input signals\n", input_set.size());

		// Build CE as OR of all input signals
		// CE = 1 when any input is 1 (meaning: update the register)
		// CE = 0 when all inputs are 0 (meaning: hold, since D == Q)
		SigSpec ce_inputs;
		for (auto bit : input_set)
			ce_inputs.append(bit);

		SigBit ce_signal;
		if (GetSize(ce_inputs) == 1) {
			ce_signal = ce_inputs[0];
		} else {
			// Create OR gate: CE = |input_set
			Wire *ce_wire = module->addWire(NEW_ID);
			module->addReduceOr(NEW_ID, ce_inputs, ce_wire);
			ce_signal = ce_wire;
		}

		// Set the CE on the FF
		ff.has_ce = true;
		ff.sig_ce = ce_signal;
		ff.pol_ce = true;  // Active high

		log("  CE signal: %s\n", log_signal(ce_signal));
	}

	// Process a single FF to find and insert CE
	bool process_ff(Cell *cell)
	{
		FfData ff(nullptr, cell);

		// Skip if already has CE, or doesn't have clock/data
		if (ff.has_ce) {
			log_debug("  Skipping %s: already has CE\n", log_id(cell));
			return false;
		}
		if (!ff.has_clk) {
			log_debug("  Skipping %s: no clock\n", log_id(cell));
			return false;
		}
		if (GetSize(ff.sig_d) == 0 || GetSize(ff.sig_q) == 0) {
			log_debug("  Skipping %s: no D or Q\n", log_id(cell));
			return false;
		}

		log("Processing FF: %s\n", log_id(cell));

		// Start with direct inputs of D
		pool<SigBit> input_set = get_input_cone(ff.sig_d, 1);
		
		// Remove Q from input set (it's the feedback, not a control signal)
		for (auto bit : sigmap(ff.sig_q))
			input_set.erase(bit);

		if (input_set.empty()) {
			log_debug("  No inputs to D (besides Q)\n");
			return false;
		}

		log_debug("  Initial input set has %zu signals\n", input_set.size());

		// Try to find enable
		if (determine_enable_recursive(input_set, ff.sig_d, ff.sig_q, 1)) {
			// Remove Q bits again (in case BFS added them back)
			for (auto bit : sigmap(ff.sig_q))
				input_set.erase(bit);

			create_ce_logic(input_set, ff);
			
			// Emit the modified FF
			ff.emit();
			return true;
		}

		log_debug("  Could not find enable for %s\n", log_id(cell));
		return false;
	}
};

void dump_flipflops_to_file(RTLIL::Design *design, const std::string &filename)
{
	std::ofstream outfile(filename);
	if (!outfile.is_open()) {
		log_error("Cannot open file %s for writing\n", filename.c_str());
		return;
	}

	for (auto module : design->selected_modules()) {
		outfile << "Module: " << log_id(module) << "\n";
		log("Module: %s\n", log_id(module));

		for (auto cell : module->cells()) {
			if (cell->is_builtin_ff()) {
				outfile << "  FF: " << log_id(cell) << " (type: " << log_id(cell->type) << ")\n";
				log("  FF: %s (type: %s)\n", log_id(cell), log_id(cell->type));
			}
		}
		outfile << "\n";
	}

	outfile.close();
	log("Wrote flip-flop list to %s\n", filename.c_str());
}

struct SatClockgatePass : public Pass {
	SatClockgatePass() : Pass("sat_clockgate", "SAT-based inferred clock gating") { }

	void help() override
	{
		log("\n");
		log("    sat_clockgate [options] [selection]\n");
		log("\n");
		log("This command performs SAT-based inferred clock gating insertion.\n");
		log("It analyzes flip-flops without explicit clock enables and uses SAT\n");
		log("to find input conditions under which D == Q (register holds value).\n");
		log("These conditions become the inferred clock enable.\n");
		log("\n");
		log("    -threshold <n>\n");
		log("        minimum number of FFs that must share an enable for clock gating\n");
		log("        to be inserted (default: 1)\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing SAT_CLOCKGATE pass (SAT-based inferred clock gating).\n");

		int threshold = 1;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-threshold" && argidx+1 < args.size()) {
				threshold = std::stoi(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		log("Using threshold: %d\n", threshold);

		// Dump all flip-flops to file (debug)
		dump_flipflops_to_file(design, "flip_flops.txt");

		int total_converted = 0;

		for (auto module : design->selected_modules()) {
			log("Processing module %s...\n", log_id(module));

			SatClockgateWorker worker(module);

			// Collect FFs to process (can't modify while iterating)
			std::vector<Cell*> ffs_to_process;
			for (auto cell : module->cells()) {
				if (cell->is_builtin_ff())
					ffs_to_process.push_back(cell);
			}

			int converted = 0;
			for (auto cell : ffs_to_process) {
				if (worker.process_ff(cell))
					converted++;
			}

			if (converted > 0) {
				log("Converted %d FFs in module %s\n", converted, log_id(module));
				total_converted += converted;
			}
		}

		log("Total FFs with inferred CE: %d\n", total_converted);

		// TODO: Call clockgate pass to convert CEs to ICG cells
		// if (total_converted >= threshold) {
		//     Pass::call(design, "clockgate");
		// }
	}
} SatClockgatePass;

PRIVATE_NAMESPACE_END
