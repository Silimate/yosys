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
 */

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/ff.h"
#include "kernel/satgen.h"
#include <queue>
#include <algorithm>
#include <fstream>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Profile all flip-flops and write to file
void profileFlipFlops(Module *module, const std::string &filename, const std::string &label)
{
	std::ofstream out(filename, std::ios::app);
	out << "\n=== " << label << " ===\n";
	out << "Module: " << log_id(module) << "\n\n";
	
	int total_ffs = 0;
	int ffs_with_ce = 0;
	int ffs_with_arst = 0;
	int ffs_with_srst = 0;
	int total_bits = 0;
	int bits_with_ce = 0;
	
	for (auto cell : module->cells()) {
		if (!cell->type.in(ID($ff), ID($dff), ID($dffe), ID($adff), ID($adffe),
		                   ID($sdff), ID($sdffe), ID($sdffce), ID($dffsr),
		                   ID($dffsre), ID($_DFF_P_), ID($_DFF_N_), ID($_DFFE_PP_),
		                   ID($_DFFE_PN_), ID($_DFFE_NP_), ID($_DFFE_NN_)))
			continue;
		
		FfData ff(nullptr, cell);
		total_ffs++;
		total_bits += ff.width;
		
		out << "FF: " << log_id(cell) << "\n";
		out << "  type:     " << log_id(cell->type) << "\n";
		out << "  width:    " << ff.width << "\n";
		out << "  has_clk:  " << (ff.has_clk ? "yes" : "no") << "\n";
		out << "  has_ce:   " << (ff.has_ce ? "yes" : "no");
		if (ff.has_ce) {
			out << " (sig_ce: " << log_signal(ff.sig_ce) << ", pol: " << (ff.pol_ce ? "active-high" : "active-low") << ")";
			ffs_with_ce++;
			bits_with_ce += ff.width;
		}
		out << "\n";
		out << "  has_arst: " << (ff.has_arst ? "yes" : "no");
		if (ff.has_arst) {
			out << " (sig_arst: " << log_signal(ff.sig_arst) << ")";
			ffs_with_arst++;
		}
		out << "\n";
		out << "  has_srst: " << (ff.has_srst ? "yes" : "no");
		if (ff.has_srst) {
			out << " (sig_srst: " << log_signal(ff.sig_srst) << ")";
			ffs_with_srst++;
		}
		out << "\n";
		out << "  sig_clk:  " << log_signal(ff.sig_clk) << "\n";
		out << "  sig_d:    " << log_signal(ff.sig_d) << "\n";
		out << "  sig_q:    " << log_signal(ff.sig_q) << "\n";
		out << "\n";
	}
	
	out << "--- Summary ---\n";
	out << "Total FFs:      " << total_ffs << "\n";
	out << "Total bits:     " << total_bits << "\n";
	out << "FFs with CE:    " << ffs_with_ce << " (" << (total_ffs ? 100*ffs_with_ce/total_ffs : 0) << "%)\n";
	out << "Bits with CE:   " << bits_with_ce << " (" << (total_bits ? 100*bits_with_ce/total_bits : 0) << "%)\n";
	out << "FFs with ARST:  " << ffs_with_arst << "\n";
	out << "FFs with SRST:  " << ffs_with_srst << "\n";
	out << "\n";
	
	out.close();
}

// Configuration
static const int DEFAULT_MAX_COVER = 100;      // Max candidate signals to consider
static const int DEFAULT_MIN_REGS = 3;         // Min registers per clock gate
static const int DEFAULT_SIM_ITERATIONS = 10;  // Random simulation iterations for pruning

struct SatClockgateWorker
{
	Module *module;
	SigMap sigmap;
	
	// Configuration
	int max_cover;
	int min_regs;
	int sim_iterations;
	
	// Maps output signal bits to their driver cells
	dict<SigBit, Cell*> sig_to_driver;
	
	// Maps cell input pins to their source signals
	dict<SigBit, pool<Cell*>> sig_to_sinks;
	
	// SAT solver and generator - created once per module
	ezSatPtr ez;
	SatGen satgen;
	
	// Statistics
	int accepted_count = 0;
	int rejected_sim_count = 0;
	int rejected_sat_count = 0;
	
	SatClockgateWorker(Module *module, int max_cover, int min_regs, int sim_iterations)
		: module(module), sigmap(module), 
		  max_cover(max_cover), min_regs(min_regs), sim_iterations(sim_iterations),
		  ez(), satgen(ez.get(), &sigmap)
	{
		// Build driver and sink maps
		for (auto cell : module->cells()) {
			for (auto &conn : cell->connections()) {
				if (cell->output(conn.first)) {
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							sig_to_driver[bit] = cell;
				}
				if (cell->input(conn.first)) {
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							sig_to_sinks[bit].insert(cell);
				}
			}
		}
		
		// Import all cells once - circuit constraints are permanent
		for (auto cell : module->cells())
			if (!cell->type.in(ID($ff), ID($dff), ID($dffe), ID($adff), ID($adffe),
			                   ID($sdff), ID($sdffe), ID($sdffce), ID($dffsr), 
			                   ID($dffsre), ID($_DFF_P_), ID($_DFF_N_), ID($_DFFE_PP_),
			                   ID($_DFFE_PN_), ID($_DFFE_NP_), ID($_DFFE_NN_)))
				satgen.importCell(cell);
	}
	
	// Get downstream signals from a register (BFS forward through combinational logic)
	pool<SigBit> getDownstreamSignals(Cell *reg, int limit)
	{
		pool<SigBit> visited;
		std::queue<SigBit> worklist;
		
		// Start from register output Q
		FfData ff(nullptr, reg);
		for (auto bit : sigmap(ff.sig_q)) {
			if (bit.wire) {
				worklist.push(bit);
				visited.insert(bit);
			}
		}
		
		while (!worklist.empty() && (int)visited.size() < limit) {
			SigBit bit = worklist.front();
			worklist.pop();
			
			// Find cells driven by this signal
			for (auto sink_cell : sig_to_sinks[bit]) {
				// Skip registers - don't traverse through them
				if (sink_cell->type.in(ID($ff), ID($dff), ID($dffe), ID($adff), ID($adffe),
				                        ID($sdff), ID($sdffe), ID($sdffce), ID($dffsr),
				                        ID($dffsre), ID($_DFF_P_), ID($_DFF_N_)))
					continue;
				
				// Add outputs of this cell to worklist
				for (auto &conn : sink_cell->connections()) {
					if (sink_cell->output(conn.first)) {
						for (auto out_bit : sigmap(conn.second)) {
							if (out_bit.wire && !visited.count(out_bit)) {
								visited.insert(out_bit);
								worklist.push(out_bit);
							}
						}
					}
				}
			}
		}
		
		return visited;
	}
	
	// Get upstream signals feeding into given signals (BFS backward)
	pool<SigBit> getUpstreamSignals(const pool<SigBit> &start_signals, int limit)
	{
		pool<SigBit> visited;
		std::queue<SigBit> worklist;
		
		for (auto bit : start_signals) {
			worklist.push(bit);
			visited.insert(bit);
		}
		
		while (!worklist.empty() && (int)visited.size() < limit) {
			SigBit bit = worklist.front();
			worklist.pop();
			
			// Find driver cell
			if (!sig_to_driver.count(bit))
				continue;
			
			Cell *driver = sig_to_driver[bit];
			
			// Skip registers
			if (driver->type.in(ID($ff), ID($dff), ID($dffe), ID($adff), ID($adffe),
			                    ID($sdff), ID($sdffe), ID($sdffce), ID($dffsr),
			                    ID($dffsre), ID($_DFF_P_), ID($_DFF_N_)))
				continue;
			
			// Add inputs of driver to worklist
			for (auto &conn : driver->connections()) {
				if (driver->input(conn.first)) {
					for (auto in_bit : sigmap(conn.second)) {
						if (in_bit.wire && !visited.count(in_bit)) {
							visited.insert(in_bit);
							worklist.push(in_bit);
						}
					}
				}
			}
		}
		
		return visited;
	}
	
	// Check if a candidate signal is a valid gating condition using SAT
	// Safe gating check: sig=1 → D==Q (i.e., (sig ∧ (D≠Q)) is UNSAT)
	bool isValidGatingSignal(SigBit candidate, SigSpec sig_d, SigSpec sig_q, bool as_enable)
	{
		std::vector<int> d_vec = satgen.importSigSpec(sig_d);
		std::vector<int> q_vec = satgen.importSigSpec(sig_q);
		int cand_var = satgen.importSigSpec(SigSpec(candidate))[0];
		
		// D != Q
		int d_ne_q = ez->vec_ne(d_vec, q_vec);
		
		// For clock enable (active high): when enable=0, D must equal Q
		// Check: (!enable ∧ (D≠Q)) is UNSAT
		// For clock disable (active low): when disable=1, D must equal Q  
		// Check: (disable ∧ (D≠Q)) is UNSAT
		
		int gating_active = as_enable ? ez->NOT(cand_var) : cand_var;
		int query = ez->AND(gating_active, d_ne_q);
		
		std::vector<int> assumptions = {query};
		std::vector<int> dummy_exprs;
		std::vector<bool> dummy_vals;
		
		return !ez->solve(dummy_exprs, dummy_vals, assumptions);
	}
	
	// Simple random simulation test to quickly prune candidates
	// bool simulationTest(SigBit candidate, SigSpec sig_d, SigSpec sig_q, bool as_enable)
	// {
	// 	// For now, skip simulation and go straight to SAT
	// 	// TODO: Implement random simulation for faster pruning
	// 	return true;
	// }
	
	// Binary search to minimize the gating condition set
	// Tries to remove half of the signals at a time
	void minimizeGatingCondition(
		std::vector<SigBit> &good_conds,
		std::vector<SigBit>::iterator begin,
		std::vector<SigBit>::iterator end,
		SigSpec sig_d, SigSpec sig_q, bool as_enable)
	{
		int half_len = (end - begin) / 2;
		if (half_len == 0)
			return;
		
		auto mid = begin + half_len;
		
		// Try removing [mid, end) from the condition
		std::vector<SigBit> test_conds;
		test_conds.insert(test_conds.end(), good_conds.begin(), begin);
		test_conds.insert(test_conds.end(), begin, mid);
		test_conds.insert(test_conds.end(), end, good_conds.end());
		
		if (!test_conds.empty() && isValidGatingSet(test_conds, sig_d, sig_q, as_enable)) {
			// Can remove [mid, end)
			good_conds.erase(mid, end);
			// Recurse on remaining half
			minimizeGatingCondition(good_conds, begin, begin + half_len, sig_d, sig_q, as_enable);
		} else {
			// Cannot remove all of [mid, end), try to minimize each half
			if (end - mid > 1)
				minimizeGatingCondition(good_conds, mid, end, sig_d, sig_q, as_enable);
			minimizeGatingCondition(good_conds, begin, mid, sig_d, sig_q, as_enable);
		}
	}
	
	// Check if OR/AND of signals forms a valid gating condition
	bool isValidGatingSet(const std::vector<SigBit> &conds, SigSpec sig_d, SigSpec sig_q, bool as_enable)
	{
		if (conds.empty())
			return false;
		
		std::vector<int> d_vec = satgen.importSigSpec(sig_d);
		std::vector<int> q_vec = satgen.importSigSpec(sig_q);
		
		// Build OR (for enable) or AND (for disable) of condition signals
		std::vector<int> cond_vars;
		for (auto bit : conds)
			cond_vars.push_back(satgen.importSigSpec(SigSpec(bit))[0]);
		
		int combined_cond;
		if (as_enable) {
			// Clock enable: OR of signals (any signal high = enable)
			combined_cond = ez->expression(ezSAT::OpOr, cond_vars);
		} else {
			// Clock disable: AND of signals (all signals high = disable)
			combined_cond = ez->expression(ezSAT::OpAnd, cond_vars);
		}
		
		int d_ne_q = ez->vec_ne(d_vec, q_vec);
		
		// Safe gating: when gating is active (enable=0 or disable=1), D must equal Q
		int gating_active = as_enable ? ez->NOT(combined_cond) : combined_cond;
		int query = ez->AND(gating_active, d_ne_q);
		
		std::vector<int> assumptions = {query};
		std::vector<int> dummy_exprs;
		std::vector<bool> dummy_vals;
		
		return !ez->solve(dummy_exprs, dummy_vals, assumptions);
	}
	
	// Find gating condition for a register
	// Returns empty vector if no valid condition found
	std::pair<std::vector<SigBit>, bool> findGatingCondition(Cell *reg)
	{
		FfData ff(nullptr, reg);
		
		// Get candidate signals downstream of this register
		pool<SigBit> downstream = getDownstreamSignals(reg, max_cover);
		
		if (downstream.empty()) {
			log_debug("  No downstream candidates for %s\n", log_id(reg));
			return {{}, false};
		}
		
		// Also include upstream signals that could affect D
		pool<SigBit> d_inputs;
		for (auto bit : sigmap(ff.sig_d))
			if (bit.wire)
				d_inputs.insert(bit);
		pool<SigBit> upstream = getUpstreamSignals(d_inputs, max_cover);
		
		// Combine and limit candidates
		std::vector<SigBit> candidates;
		for (auto bit : downstream)
			candidates.push_back(bit);
		for (auto bit : upstream)
			if (!downstream.count(bit))
				candidates.push_back(bit);
		
		if ((int)candidates.size() > max_cover)
			candidates.resize(max_cover);
		
		log_debug("  Found %zu candidate signals\n", candidates.size());
		
		// Try as clock enable first (more common)
		if (isValidGatingSet(candidates, ff.sig_d, ff.sig_q, true)) {
			minimizeGatingCondition(candidates, candidates.begin(), candidates.end(),
			                        ff.sig_d, ff.sig_q, true);
			if (!candidates.empty()) {
				return {candidates, true};  // true = clock enable
			}
		}
		
		// Try as clock disable
		if (isValidGatingSet(candidates, ff.sig_d, ff.sig_q, false)) {
			minimizeGatingCondition(candidates, candidates.begin(), candidates.end(),
			                        ff.sig_d, ff.sig_q, false);
			if (!candidates.empty()) {
				return {candidates, false};  // false = clock disable
			}
		}
		
		rejected_sat_count++;
		return {{}, false};
	}
	
	// Insert clock gating logic for a group of registers
	void insertClockGate(const std::vector<Cell*> &regs, 
	                     const std::vector<SigBit> &gating_conds,
	                     bool as_enable)
	{
		if (regs.empty() || gating_conds.empty())
			return;
		
		log("  Inserting clock gate for %zu registers with %zu condition signals\n",
		    regs.size(), gating_conds.size());
		
		// Build gating condition: OR for enable, AND for disable
		SigBit gating_signal;
		if (gating_conds.size() == 1) {
			gating_signal = gating_conds[0];
		} else {
			SigSpec cond_inputs;
			for (auto bit : gating_conds)
				cond_inputs.append(bit);
			
			Wire *cond_wire = module->addWire(NEW_ID);
			if (as_enable)
				module->addReduceOr(NEW_ID, cond_inputs, cond_wire);
			else
				module->addReduceAnd(NEW_ID, cond_inputs, cond_wire);
			gating_signal = cond_wire;
		}
		
		// If disable signal, invert to get enable
		if (!as_enable) {
			Wire *inv_wire = module->addWire(NEW_ID);
			module->addNot(NEW_ID, gating_signal, inv_wire);
			gating_signal = inv_wire;
		}
		
		// Add CE to each register
		for (auto reg : regs) {
			FfData ff(nullptr, reg);
			
			if (ff.has_ce) {
				// Already has CE, AND with new condition
				Wire *combined_ce = module->addWire(NEW_ID);
				module->addAnd(NEW_ID, ff.sig_ce, gating_signal, combined_ce);
				ff.sig_ce = combined_ce;
			} else {
				ff.has_ce = true;
				ff.sig_ce = gating_signal;
				ff.pol_ce = true;
			}
			
			ff.emit();
		}
	}
	
	// Main processing function
	void run()
	{
		log("Processing module %s\n", log_id(module));
		
		// Collect all registers
		std::vector<Cell*> registers;
		for (auto cell : module->cells()) {
			if (!cell->type.in(ID($ff), ID($dff), ID($dffe), ID($adff), ID($adffe),
			                   ID($sdff), ID($sdffe), ID($sdffce), ID($dffsr),
			                   ID($dffsre), ID($_DFF_P_), ID($_DFF_N_), ID($_DFFE_PP_),
			                   ID($_DFFE_PN_), ID($_DFFE_NP_), ID($_DFFE_NN_)))
				continue;
			
			FfData ff(nullptr, cell);
			
			// Skip registers that already have CE
			if (ff.has_ce) {
				log_debug("  Skipping %s: already has CE\n", log_id(cell));
				continue;
			}
			
			if (!ff.has_clk) {
				log_debug("  Skipping %s: no clock\n", log_id(cell));
				continue;
			}
			
			registers.push_back(cell);
		}
		
		log("  Found %zu registers without CE\n", registers.size());
		
		// Track accepted gating conditions for reuse
		// Key: (sorted literal IDs, is_enable) -> (condition signals, registers)
		std::map<std::pair<std::vector<int>, bool>, std::pair<std::vector<SigBit>, std::vector<Cell*>>> accepted_gates;
		
		int processed = 0;
		for (auto reg : registers) {
			if (processed % 100 == 0 && processed > 0)
				log("  Processed %d/%zu registers\n", processed, registers.size());
			processed++;
			
			log_debug("Processing register %s\n", log_id(reg));
			
			auto [gating_conds, is_enable] = findGatingCondition(reg);
			
			if (gating_conds.empty()) {
				log_debug("  No valid gating condition found\n");
				continue;
			}
			
			// Create signature for this gating condition (sorted literal IDs for permutation invariance)
			std::vector<int> sorted_ids;
			sorted_ids.reserve(gating_conds.size());
			for (auto bit : gating_conds)
				sorted_ids.push_back(satgen.importSigSpec(SigSpec(bit))[0]);
			std::sort(sorted_ids.begin(), sorted_ids.end());
			
			auto key = std::make_pair(std::move(sorted_ids), is_enable);
			
			// Check if we already have this condition
			auto it = accepted_gates.find(key);
			if (it != accepted_gates.end()) {
				it->second.second.push_back(reg);
				log_debug("  Reusing existing gating condition for %s\n", log_id(reg));
			} else {
				accepted_gates[key] = {gating_conds, {reg}};
				log("  Found new gating condition for %s (%s)\n",
				    log_id(reg), is_enable ? "enable" : "disable");
			}
		}
		
		// Insert clock gates for groups that meet minimum register threshold
		int gates_inserted = 0;
		for (auto &[key, data] : accepted_gates) {
			bool is_enable = key.second;
			auto &[conds, regs] = data;
			
			if ((int)regs.size() >= min_regs) {
				insertClockGate(regs, conds, is_enable);
				gates_inserted++;
				accepted_count += regs.size();
			} else {
				log_debug("  Skipping gating condition (only %zu registers, need %d)\n",
				          regs.size(), min_regs);
			}
		}
		
		log("  Inserted %d clock gates\n", gates_inserted);
		log("  Statistics: accepted=%d, rejected_sat=%d\n",
		    accepted_count, rejected_sat_count);
		log("  SAT stats: literals=%d, expressions=%d\n",
		    ez->numLiterals(), ez->numExpressions());
	}
};

struct SatClockgatePass : public Pass {
	SatClockgatePass() : Pass("sat_clockgate", "SAT-based automatic clock gating") { }
	
	void help() override
	{
		log("\n");
		log("    sat_clockgate [options] [selection]\n");
		log("\n");
		log("This command performs SAT-based automatic clock gating insertion.\n");
		log("It analyzes registers and uses SAT solving to find signals that can\n");
		log("serve as clock enable conditions (when the signal is low, D==Q).\n");
		log("\n");
		log("Algorithm based on:\n");
		log("  - \"Automatic Synthesis of Clock Gating Logic\" by Aaron P. Hurst\n");
		log("  - OpenROAD's cgt module implementation\n");
		log("\n");
		log("    -max_cover <n>\n");
		log("        maximum number of candidate signals to consider per register\n");
		log("        (default: %d)\n", DEFAULT_MAX_COVER);
		log("\n");
		log("    -min_regs <n>\n");
		log("        minimum number of registers that must share a gating condition\n");
		log("        for a clock gate to be inserted (default: %d)\n", DEFAULT_MIN_REGS);
		log("\n");
	}
	
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing SAT_CLOCKGATE pass.\n");
		
		int max_cover = DEFAULT_MAX_COVER;
		int min_regs = DEFAULT_MIN_REGS;
		int sim_iterations = DEFAULT_SIM_ITERATIONS;
		
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-max_cover" && argidx+1 < args.size()) {
				max_cover = std::stoi(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-min_regs" && argidx+1 < args.size()) {
				min_regs = std::stoi(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);
		
		log("Configuration: max_cover=%d, min_regs=%d\n", max_cover, min_regs);
		
		// Clear profile file and write header
		std::ofstream clear_file("ff_profile.txt", std::ios::trunc);
		clear_file << "Flip-Flop Profile Report\n";
		clear_file << "========================\n";
		clear_file.close();
		
		int total_gates = 0;
		
		for (auto module : design->selected_modules()) {
			// Profile BEFORE clock gating
			profileFlipFlops(module, "ff_profile.txt", "BEFORE sat_clockgate");
			
			SatClockgateWorker worker(module, max_cover, min_regs, sim_iterations);
			worker.run();
			total_gates += worker.accepted_count;
			
			// Profile AFTER clock gating
			profileFlipFlops(module, "ff_profile.txt", "AFTER sat_clockgate");
		}
		
		log("Total clock gates inserted: %d\n", total_gates);
		
		// Convert CEs to actual clock gate cells
		Pass::call(design, "clockgate");
	}
} SatClockgatePass;

PRIVATE_NAMESPACE_END
