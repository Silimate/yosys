/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *  Copyright (C) 2020  Marcelina Kościelnicka <mwk@0x04.net>
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

#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/ff.h"
#include "passes/opt/dff/opt_dff.h"
#include <stdio.h>
#include <stdlib.h>

USING_YOSYS_NAMESPACE

YOSYS_NAMESPACE_BEGIN

OptDffWorker::OptDffWorker(const OptDffOptions &opt, Module *mod, int64_t sat_effort)
	: opt(opt), module(mod), sigmap(mod), initvals(&sigmap, mod), sat_budget(sat_effort)
{
}

void OptDffWorker::remove_ff_bits(Cell *cell, const pool<int> &drop)
{
	modwalker_ptr.reset();

	FfData ff(&initvals, cell);
	std::vector<int> keep;
	for (int i = 0; i < ff.width; i++)
		if (!drop.count(i))
			keep.push_back(i);

	FfData new_ff = ff.slice(keep);
	new_ff.cell = cell;
	new_ff.emit();
}

YOSYS_NAMESPACE_END

PRIVATE_NAMESPACE_BEGIN

struct OptDffPass : public Pass {
	OptDffPass() : Pass("opt_dff", "perform DFF optimizations") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_dff [-nodffe] [-nosdff] [-keepdc] [-sat] [selection]\n");
		log("\n");
		log("This pass converts flip-flops to a more suitable type by merging clock enables\n");
		log("and synchronous reset multiplexers, removing unused control inputs, or\n");
		log("potentially removes the flip-flop altogether, converting it to a constant\n");
		log("driver.\n");
		log("\n");
		log("    -nodffe\n");
		log("        disables dff -> dffe conversion, and other transforms recognizing clock\n");
		log("        enable\n");
		log("\n");
		log("    -nosdff\n");
		log("        disables dff -> sdff conversion, and other transforms recognizing sync\n");
		log("        resets\n");
		log("\n");
		log("    -simple-dffe\n");
		log("        only enables clock enable recognition transform for obvious cases\n");
		log("\n");
		log("    -sat\n");
		log("        additionally invoke SAT solver to detect and remove flip-flops (with\n");
		log("        non-constant inputs) that can also be replaced with a constant driver,\n");
		log("        or merged with equivalent flip-flops. this reasons in 2-valued logic\n");
		log("        and may resolve don't-care bits, so it is incompatible with -keepdc.\n");
		log("        the scratchpad option 'opt_dff.sat_effort' (solver propagation steps,\n");
		log("        default 1000000000, 0 = unlimited) deterministically bounds the total\n");
		log("        sat effort spent per module, remaining proofs are skipped once exceeded.\n");
		log("        when 'opt_dff.sat_effort_pool' is set, every module in every later\n");
		log("        -sat call also draws from that one design-wide pool, which is written\n");
		log("        back after each call; once it reaches 0, -sat skips its proofs.\n");
		log("\n");
		log("    -keepdc\n");
		log("        some optimizations change the behavior of the circuit with respect to\n");
		log("        don't-care bits. for example in 'a+0' a single x-bit in 'a' will cause\n");
		log("        all result bits to be set to x. this behavior changes when 'a+0' is\n");
		log("        replaced by 'a'. the -keepdc option disables all such optimizations.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_DFF pass (perform DFF optimizations).\n");

		OptDffOptions opt;
		opt.nodffe = false;
		opt.nosdff = false;
		opt.simple_dffe = false;
		opt.keepdc = false;
		opt.sat = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-nodffe") { opt.nodffe = true; continue; }
			if (args[argidx] == "-nosdff") { opt.nosdff = true; continue; }
			if (args[argidx] == "-simple-dffe") { opt.simple_dffe = true; continue; }
			if (args[argidx] == "-keepdc") { opt.keepdc = true; continue; }
			if (args[argidx] == "-sat") { opt.sat = true; continue; }
			break;
		}
		extra_args(args, argidx, design);

		// The SAT engine reasons in 2-valued logic (a constant x is treated as
		// 0), so it can resolve don't-care bits to concrete values -- exactly
		// what -keepdc promises not to do. Refuse the combination rather than
		// silently ignore -keepdc.
		if (opt.sat && opt.keepdc)
			log_cmd_error("The -sat and -keepdc options are mutually exclusive.\n");

		// The pool, when set, is shared by every opt_dff -sat call until it is reset, so
		// the total effort stays bounded however many modules or calls there are
		const std::string pool_key = "opt_dff.sat_effort_pool";
		int64_t per_module = design->scratchpad_get_int("opt_dff.sat_effort", 1000000000);
		bool pooled = opt.sat && design->scratchpad.count(pool_key);
		int64_t pool = 0;
		if (pooled) {
			const std::string &value = design->scratchpad.at(pool_key);
			char *end = nullptr;
			pool = strtoll(value.c_str(), &end, 10);
			if (value.empty() || *end != '\0')
				log_cmd_error("Scratchpad option '%s' expects an integer, got '%s'.\n", pool_key.c_str(), value.c_str());
		}
		int64_t pool_start = pool, spent_total = 0;

		bool did_something = false;
		for (auto mod : design->selected_modules()) {
			// each module draws at most what the pool has left, and an empty pool turns -sat off
			OptDffOptions mod_opt = opt;
			int64_t effort = per_module;
			if (pooled) {
				mod_opt.sat = pool > 0;
				effort = per_module > 0 ? std::min(per_module, pool) : pool;
			}
			OptDffWorker worker(mod_opt, mod, effort);
			if (worker.run())
				did_something = true;
			// constbits also runs without -sat: it folds bits with all-constant
			// inputs, -sat additionally proves bits with wire inputs
			if (worker.run_constbits())
				did_something = true;
			if (mod_opt.sat && worker.run_eqbits())
				did_something = true;
			if (mod_opt.sat && worker.sat_budget.enabled()) {
				int64_t spent = worker.sat_budget.total - worker.sat_budget.remaining;
				spent_total += spent;
				pool -= spent;
			}
		}

		if (spent_total > 0)
			log("opt_dff -sat: spent %lld solver steps.\n", (long long)spent_total);
		if (pooled) {
			if (pool_start > 0 && pool <= 0)
				log_warning("opt_dff -sat: the design-wide solver effort pool is used up, so later "
						"-sat calls skip their proofs. Raise the scratchpad option '%s'.\n", pool_key.c_str());
			design->scratchpad_set_string(pool_key, std::to_string(std::max(pool, (int64_t)0)));
		}

		if (did_something)
			design->scratchpad_set_bool("opt.did_something", true);
	}
} OptDffPass;

PRIVATE_NAMESPACE_END
