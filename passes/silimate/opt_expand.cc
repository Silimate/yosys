/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *                      Akash Levy <akash@silimate.com>
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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool did_something;

#include "passes/silimate/peepopt_expand.h"

struct OptExpandPass : public Pass {
  OptExpandPass() : Pass("opt_expand", "expand conjunction") { }
  void help() override
  {
    //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
    log("\n");
    log("    opt_expand [selection]\n");
    log("\n");
    log("This pass expands conjunction (AND) operations into disjunction (OR).\n");
    log("\n");
    log("y = (a | b) & c   ===>   y = (a & c) | (b & c)\n");
    log("\n");
    log("    -max_iters n\n");
		log("        max number of pass iterations to run.\n");
		log("\n");
  }
  void execute(std::vector<std::string> args, RTLIL::Design *design) override
  {
    log_header(design, "Executing OPT_EXPAND pass (expand conjunction into disjunction).\n");

    size_t argidx;
    int max_iters = 10000;
    for (argidx = 1; argidx < args.size(); argidx++) {
      // No extra arguments
      if (args[argidx] == "-max_iters" && argidx + 1 < args.size()) {
        max_iters = std::stoi(args[++argidx]);
        continue;
      }
      break;
    }
    extra_args(args, argidx, design);
    for (auto module : design->selected_modules())
    {
      did_something = true;
      for (int i = 0; did_something && i < max_iters; i++)
      {
        log("ITERATION OF OPT_EXPAND\n");
        did_something = false;
        peepopt_pm pm(module);
        pm.setup(module->selected_cells());
        pm.run_expand();
      }
    }
  }
} PeepoptPass;

PRIVATE_NAMESPACE_END
