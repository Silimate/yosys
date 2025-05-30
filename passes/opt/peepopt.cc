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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/utils.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool did_something;

// scratchpad configurations for pmgen
int shiftadd_max_ratio;

// Helper function, removes LSB 0s
SigSpec remove_bottom_padding(SigSpec sig)
{
	int i = 0;
	for (; i < sig.size() - 1 && sig[i] == State::S0; i++);
	return sig.extract(i, sig.size() - i);
}

#include "passes/opt/peepopt_pm.h"

struct PeepoptPass : public Pass {
	PeepoptPass() : Pass("peepopt", "collection of peephole optimizers") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    peepopt [options] [selection]\n");
		log("\n");
		log("This pass applies a collection of peephole optimizers to the current design.\n");
		log("\n");
		log("This pass employs the following rules by default:\n");
		log("\n");
		log("   * muldiv - Replace (A*B)/B with A\n");
		log("\n");
		log("   * muldiv_c - Replace (A*B)/C with A*(B/C) when C is a const divisible by B.\n");
		log("\n");
		log("   * shiftmul - Replace A>>(B*C) with A'>>(B<<K) where C and K are constants\n");
		log("                and A' is derived from A by appropriately inserting padding\n");
		log("                into the signal. (right variant)\n");
		log("\n");
		log("                Analogously, replace A<<(B*C) with appropriate selection of\n");
		log("                output bits from A<<(B<<K). (left variant)\n");
		log("\n");
		log("   * shiftadd - Replace A>>(B+D) with (A'>>D)>>(B) where D is constant and\n");
		log("                A' is derived from A by padding or cutting inaccessible bits.\n");
		log("                Scratchpad: 'peepopt.shiftadd.max_data_multiple' (default: 2)\n");
		log("                limits the amount of padding to a multiple of the data, \n");
		log("                to avoid high resource usage from large temporary MUX trees.\n");
		log("\n");
		log("If -formalclk is specified it instead employs the following rules:\n");
		log("\n");
		log("   * clockgateff - Replace latch based clock gating patterns with a flip-flop\n");
		log("                   based pattern to prevent combinational paths from the\n");
		log("                   output to the enable input after running clk2fflogic.\n");
		log("\n");
		log("If -muxorder is specified it adds the following rule:\n");
		log("\n");
		log("   * muxorder - Replace S?(A OP B):A with A OP (S?B:I) where I is identity of OP\n");
		log("                Ex 1:   S?(A + B):A   --->   A + (S?B:0)\n");
		log("                Ex 2:   S?(A * B):A   --->   A & (S?B:1)\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing PEEPOPT pass (run peephole optimizers).\n");

		bool formalclk = false;
		bool muxorder = false;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-formalclk") {
				formalclk = true;
				continue;
			}
			if (args[argidx] == "-muxorder") {
				muxorder = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		// limit the padding from shiftadd to a multiple of the input data
		// during techmap it creates (#data + #padding) * log(shift) $_MUX_ cells
		// 2x implies there is a constant shift larger than the input-data which should be extremely rare
		shiftadd_max_ratio = design->scratchpad_get_int("peepopt.shiftadd.max_data_multiple", 2);

		for (auto module : design->selected_modules())
		{
			did_something = true;

			while (did_something)
			{
				did_something = false;

				peepopt_pm pm(module);

				pm.setup(module->selected_cells());

				if (formalclk) {
					pm.run_formal_clockgateff();
				} else {
					pm.run_shiftadd();
					pm.run_shiftmul_right();
					pm.run_shiftmul_left();
					pm.run_muldiv();
					pm.run_muldiv_c();
					pm.run_sub_neg();
					if (muxorder)
						pm.run_muxorder();
				}
			}
		}
	}
} PeepoptPass;

PRIVATE_NAMESPACE_END
