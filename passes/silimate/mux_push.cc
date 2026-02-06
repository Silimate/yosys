/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *                      Abhinav Tondapu <abhinav@silimate.com>
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

#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include "kernel/io.h"
#include <stdlib.h>
#include <stdio.h>
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct OptMuxPushWorker
{
  RTLIL::Design *design;
  RTLIL::Module *module;
  SigMap sigmap;

  dict<SigBit, RTLIL::Cell*> driver_map;
  dict<SigBit, int> fanout_map;

  pool<IdString> target_types;
  int fanout_limit;
  int total_count;

  OptMuxPushWorker(RTLIL::Design *design, RTLIL::Module *module,
      const pool<IdString> &target_types, int fanout_limit) :
      design(design), module(module), sigmap(module),
      target_types(target_types), fanout_limit(fanout_limit), total_count(0)
  {
  }

  void build_connectivity()
  {
    driver_map.clear();
    fanout_map.clear();

    // Build per-bit driver and fanout maps for the current module
    for (auto cell : module->cells())
    {
      for (auto &it : cell->connections()) {
        RTLIL::SigSpec sig = sigmap(it.second);
        if (cell->output(it.first)) {
          for (auto &bit : sig) {
            if (bit.wire == nullptr)
              continue;
            auto it_drv = driver_map.find(bit);
            if (it_drv == driver_map.end()) {
              driver_map[bit] = cell;
            } else if (it_drv->second != cell) {
              driver_map[bit] = nullptr;
            }
          }
        }
        if (cell->input(it.first)) {
          for (auto &bit : sig) {
            if (bit.wire == nullptr)
              continue;
            fanout_map[bit]++;
          }
        }
      }
    }

    // Treat module output ports as consumers
    for (auto wire : module->wires()) {
      if (!wire->port_output)
        continue;
      RTLIL::SigSpec sig = sigmap(RTLIL::SigSpec(wire));
      for (auto &bit : sig) {
        if (bit.wire == nullptr)
          continue;
        fanout_map[bit]++;
      }
    }
  }

  bool sig_has_keep(const RTLIL::SigSpec &sig)
  {
    for (auto &bit : sig) {
      if (bit.wire != nullptr && bit.wire->get_bool_attribute(ID::keep))
        return true;
    }
    return false;
  }

  bool mux_drives_sig(const RTLIL::SigSpec &sig, RTLIL::Cell *&mux_cell)
  {
    mux_cell = nullptr;
    for (auto &bit : sig) {
      if (bit.wire == nullptr)
        return false;
      // Require a single consistent driver for all bits in the SigSpec
      auto it_drv = driver_map.find(bit);
      if (it_drv == driver_map.end() || it_drv->second == nullptr)
        return false;
      if (mux_cell == nullptr)
        mux_cell = it_drv->second;
      else if (mux_cell != it_drv->second)
        return false;
    }
    return mux_cell != nullptr && mux_cell->type == ID($mux);
  }

  bool fanout_within_limit(const RTLIL::SigSpec &sig)
  {
    for (auto &bit : sig) {
      if (bit.wire == nullptr)
        return false;
      // Enforce fanout cap per bit to keep the mux exclusive to this operator
      if (fanout_map[bit] > fanout_limit)
        return false;
    }
    return true;
  }

  bool fanout_is_one(const RTLIL::SigSpec &sig)
  {
    for (auto &bit : sig) {
      if (bit.wire == nullptr)
        return false;
      if (fanout_map[bit] != 1)
        return false;
    }
    return true;
  }

  void run()
  {
    while (true)
    {
      build_connectivity();

      struct candidate_t {
        RTLIL::Cell *cell = nullptr;
        RTLIL::Cell *mux_cell = nullptr;
        IdString port;
      };

      std::vector<candidate_t> candidates;

      for (auto cell : module->selected_cells())
      {
        if (!target_types.count(cell->type))
          continue;
        if (cell->get_bool_attribute(ID::keep))
          continue;

        RTLIL::SigSpec cell_out = sigmap(cell->getPort(ID::Y));
        if (sig_has_keep(cell_out))
          continue;

        // Look for one mux driven input to push through per operator
        for (auto &it : cell->connections())
        {
          if (!cell->input(it.first))
            continue;

          RTLIL::SigSpec in_sig = sigmap(it.second);
          RTLIL::Cell *mux_cell = nullptr;
          if (!mux_drives_sig(in_sig, mux_cell))
            continue;
          if (!design->selected(module, mux_cell))
            continue;
          if (mux_cell->get_bool_attribute(ID::keep))
            continue;

          RTLIL::SigSpec mux_out = sigmap(mux_cell->getPort(ID::Y));
          // Require the mux to drive the entire operator input
          if (mux_out != in_sig)
            continue;
          if (sig_has_keep(mux_out))
            continue;
          if (!fanout_within_limit(mux_out))
            continue;

          // Only push one mux per operator per iteration
          candidates.push_back({cell, mux_cell, it.first});
          break;
        }
      }

      if (candidates.empty())
        break;

      pool<RTLIL::Cell*> cells_to_remove;
      pool<RTLIL::SigBit> touched_bits;

      for (auto &cand : candidates)
      {
        RTLIL::Cell *cell = cand.cell;
        RTLIL::Cell *mux_cell = cand.mux_cell;
        RTLIL::SigSpec cand_in = sigmap(cell->getPort(cand.port));
        bool overlaps = false;
        for (auto &bit : cand_in) {
          if (touched_bits.count(bit)) {
            overlaps = true;
            break;
          }
        }
        if (overlaps)
          continue;
        // Avoid rewriting overlapping signals within a single iteration
        for (auto &bit : cand_in)
          touched_bits.insert(bit);

        log_debug("    Pushing mux %s through %s cell %s port %s.\n",
            log_id(mux_cell->name), log_id(cell->type), log_id(cell->name), log_id(cand.port));

        // Reuse the original operator as branch A to preserve the instance name and metadata
        RTLIL::Cell *branch_a = cell;

        // Create branch B with a deterministic name derived from the original
        RTLIL::IdString branch_b_name = NEW_ID2;
        RTLIL::Cell *branch_b = module->addCell(branch_b_name, cell->type);
        branch_b->parameters = cell->parameters;
        branch_b->attributes = cell->attributes;
        branch_b->set_src_attribute(cell->get_src_attribute());

        RTLIL::SigSpec orig_y = cell->getPort(ID::Y);
        std::vector<std::pair<IdString, RTLIL::SigSpec>> conns;
        for (auto &p : cell->connections())
          conns.push_back(p);
        for (auto &p : conns) {
          RTLIL::SigSpec conn_sig = p.second;
          if (p.first == cand.port) {
            branch_a->setPort(p.first, mux_cell->getPort(ID::A));
            branch_b->setPort(p.first, mux_cell->getPort(ID::B));
          } else {
            branch_a->setPort(p.first, conn_sig);
            branch_b->setPort(p.first, conn_sig);
          }
        }

        RTLIL::IdString out_a_name = NEW_ID2_SUFFIX("mpa_y");
        RTLIL::IdString out_b_name = NEW_ID2_SUFFIX("mpb_y");
        RTLIL::SigSpec out_a = module->addWire(out_a_name, GetSize(orig_y));
        RTLIL::SigSpec out_b = module->addWire(out_b_name, GetSize(orig_y));
        branch_a->setPort(ID::Y, out_a);
        branch_b->setPort(ID::Y, out_b);
        branch_a->fixup_parameters();
        branch_b->fixup_parameters();

        // Always create a new mux so other consumers of the original mux are unaffected
        RTLIL::IdString new_mux_name = NEW_ID2_SUFFIX("muxpush");
        RTLIL::Cell *new_mux = module->addMux(new_mux_name, out_a, out_b, mux_cell->getPort(ID::S), orig_y);
        new_mux->set_src_attribute(cell->get_src_attribute());

        // Remove the original mux when it becomes dead after the rewrite
        RTLIL::SigSpec mux_out = sigmap(mux_cell->getPort(ID::Y));
        if (fanout_is_one(mux_out))
          cells_to_remove.insert(mux_cell);

        total_count++;
      }

      for (auto cell : cells_to_remove)
        module->remove(cell);
    }
  }
};

struct OptMuxPushPass : public Pass {
  OptMuxPushPass() : Pass("muxpush", "push muxes through lightweight operators") { }

  void help() override
  {
    log("\n");
    log("    muxpush [options] [selection]\n");
    log("\n");
    log("Push $mux cells forward through lightweight operators by cloning\n");
    log("the operator and re-inserting the mux at the output.\n");
    log("\n");
    log("    -limit <int>\n");
    log("        maximum fanout allowed for the mux output (default: 1)\n");
    log("\n");
    log("    -types <string>\n");
    log("        comma-separated list of operator cell types to push through\n");
    log("        (default: $add,$sub,$xor)\n");
    log("\n");
  }

  void execute(std::vector<std::string> args, RTLIL::Design *design) override
  {
    int fanout_limit = 1;
    std::string types = "$add,$sub,$xor";

    log_header(design, "Executing MUXPUSH pass (push muxes through light ops).\n");

    size_t argidx;
    for (argidx = 1; argidx < args.size(); argidx++) {
      if (args[argidx] == "-limit" && argidx+1 < args.size()) {
        fanout_limit = atoi(args[++argidx].c_str());
        continue;
      }
      if (args[argidx] == "-types" && argidx+1 < args.size()) {
        types = args[++argidx];
        continue;
      }
      break;
    }
    extra_args(args, argidx, design);

    pool<IdString> target_types;
    for (auto &tok : split_tokens(types, ", \t\r\n")) {
      if (tok.empty())
        continue;
      target_types.insert(RTLIL::escape_id(tok));
    }

    int total_count = 0;
    for (auto module : design->selected_modules()) {
      if (module->get_bool_attribute(ID::blackbox))
        continue;
      OptMuxPushWorker worker(design, module, target_types, fanout_limit);
      worker.run();
      total_count += worker.total_count;
    }

    log("  Pushed muxes through %d operator inputs.\n", total_count);
  }
} OptMuxPushPass;

PRIVATE_NAMESPACE_END
