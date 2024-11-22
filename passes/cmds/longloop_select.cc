/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
#include "kernel/utils.h"
#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct LongLoopSelect : public ScriptPass {
	LongLoopSelect()
	    : ScriptPass("longloop_select", "Selects long for-loops (Creating logic above a certain logic depth) for further optimization")
	{
	}
	void script() override {}

	// Adapted from the torder pass
	void toposorting(std::vector<Cell *> &cells, SigMap &sigmap, TopoSort<IdString, RTLIL::sort_by_id_str> &toposort)
	{
		dict<SigBit, pool<IdString>> bit_drivers, bit_users;
		for (Cell *cell : cells) {
			for (auto conn : cell->connections()) {
				bool noautostop = true;
				if (!noautostop && yosys_celltypes.cell_known(cell->type)) {
					if (conn.first.in(ID::Q, ID::CTRL_OUT, ID::RD_DATA))
						continue;
					if (cell->type.in(ID($memrd), ID($memrd_v2)) && conn.first == ID::DATA)
						continue;
				}

				if (cell->input(conn.first))
					for (auto bit : sigmap(conn.second))
						bit_users[bit].insert(cell->name);

				if (cell->output(conn.first))
					for (auto bit : sigmap(conn.second))
						bit_drivers[bit].insert(cell->name);

				toposort.node(cell->name);
			}

			for (auto &it : bit_users)
				if (bit_drivers.count(it.first))
					for (auto driver_cell : bit_drivers.at(it.first))
						for (auto user_cell : it.second)
							toposort.edge(driver_cell, user_cell);

			toposort.analyze_loops = false;
			toposort.sort();
		}
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		if (design == nullptr) {
			log_error("No design object");
			return;
		}
		uint32_t threshold_depth = 100;
		bool debug = false;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-depth") {
				argidx++;
				threshold_depth = std::stoul(args[argidx], nullptr, 10);
			} else if (args[argidx] == "-debug") {
				debug = true;
			} else {
				break;
			}
		}
		extra_args(args, argidx, design);

		if (std::getenv("DEBUG_LONGLOOPS")) {
			debug = true;
		}
		log("Running longloop_select pass\n");
		log_flush();

		for (auto module : design->modules()) {
			if (debug) {
				log("Module %s\n", log_id(module));
				log_flush();
			}
			if (debug) {
				log("  Creating sigmap\n");
				log_flush();
			}
			SigMap sigmap(module);
			TopoSort<IdString, RTLIL::sort_by_id_str> toposort;
			std::vector<Cell *> cells;
			std::map<uint64_t, std::vector<Cell *>> loopIndexCellMap;
			if (debug) {
				log("  Creating sorting datastructures\n");
				log_flush();
			}
			for (auto cell : module->selected_cells()) {
				cells.push_back(cell);
				std::string loopIndex = cell->get_string_attribute("\\in_for_loop");
				if (!loopIndex.empty()) {
					uint64_t loopInd = std::stoul(loopIndex, nullptr, 10);
					std::map<uint64_t, std::vector<Cell *>>::iterator itr = loopIndexCellMap.find(loopInd);
					if (itr == loopIndexCellMap.end()) {
						std::vector<Cell *> cellSet;
						cellSet.push_back(cell);
						loopIndexCellMap.emplace(loopInd, cellSet);
					} else {
						itr->second.push_back(cell);
					}
				}
			}
			if (debug) {
				log("  Found %ld for-loop clusters\n", loopIndexCellMap.size());
				log_flush();
			}

			for (std::map<uint64_t, std::vector<Cell *>>::iterator itr = loopIndexCellMap.begin(); itr != loopIndexCellMap.end(); itr++) {
				uint64_t loopInd = itr->first;
				if (itr->second.size() < threshold_depth) {
					if (debug) {
						log("  Skipping loop id %ld as it contains only %ld cells\n", loopInd, itr->second.size());
						log_flush();
					}
					continue;
				}
				if (debug) {
					log("  Analyzing loop id %ld containing %ld cells\n", loopInd, itr->second.size());
					log_flush();
				}
				// For a given for-loop cell group, perform topological sorting to get the logic depth of the ending cell in
				// the group
				TopoSort<IdString, RTLIL::sort_by_id_str> toposort;
				toposorting(itr->second, sigmap, toposort);
				int logicdepth = 0;
				for (auto itrRank = toposort.node_to_index.begin(); itrRank != toposort.node_to_index.end(); itrRank++) {
					logicdepth = std::max(logicdepth, itrRank->second);
				}
				if (debug) {
					log("  Logic depth: %d\n", logicdepth);
					log_flush();
				}
				if (logicdepth > (int)threshold_depth) {
					std::vector<Yosys::RTLIL::IdString>::reverse_iterator itrLastCell = toposort.sorted.rbegin();
					log("  Selecting %ld cells in for-loop id %ld of depth %d ending with cell %s\n", itr->second.size(), loopInd,
					    logicdepth, log_id((*itrLastCell)));
					// Select all cells in the loop cluster
					for (auto cell : itr->second) {
						design->selected_member(module->name, cell->name);
					}
				}
			}
		}

		log("End longloop_select pass\n");
		log_flush();
	}
} LongLoopSelect;

PRIVATE_NAMESPACE_END
