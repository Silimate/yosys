/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Stan Lee <stan@silimate.com>
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
#include "cxxrtl_sim.h"

#include <atomic>
#include <thread>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct CxxrtlCompilePass : public Pass {
	CxxrtlCompilePass() : Pass("cxxrtl_compile", "compile CXXRTL evaluators in parallel") {}

	void help() override
	{
		log("\n");
		log("    cxxrtl_compile [-j <n>] <file.cc> [<file.cc> ...]\n");
		log("\n");
		log("Compile each write_cxxrtl output into a self-contained evaluator shared\n");
		log("object next to it (<file>.so), suitable for cxxrtl_sim -so. Files whose\n");
		log(".so is already up to date are skipped to save time.\n");
		log("\n");
		log("    -j <n>\n");
		log("        number of concurrent compiler processes.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, Design *design) override
	{
		log_header(design, "Executing CXXRTL_COMPILE pass.\n");

		int jobs = 1;
		std::vector<std::string> cc_paths;

		// Argument parsing
		for (size_t argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-j" && argidx+1 < args.size()) {
				jobs = std::max(1, atoi(args[++argidx].c_str()));
				continue;
			}
			cc_paths.push_back(args[argidx]);
		}

		std::vector<std::string> work;

		// Validation for each input file
		for (auto &cc_path : cc_paths) {
			if (cc_path.size() < 4 || cc_path.compare(cc_path.size()-3, 3, ".cc") != 0) // check if it is a .cc file
				log_cmd_error("'%s' is not a .cc file.\n", cc_path.c_str());
			if (!check_file_exists(cc_path)) // check if file exists
				log_cmd_error("'%s' does not exist.\n", cc_path.c_str());
			if (cxxrtl_so_up_to_date(cc_path)) // skip if the .so is up to date to avoid recompilation
				log("Up to date: %s\n", cxxrtl_so_path(cc_path).c_str());
			else
				work.push_back(cc_path);
		}

		// Exit early if no files need to be compiled due to up-to-date or invalid files
		if (work.empty()) {
			log("Nothing to compile (%d evaluators up to date).\n", GetSize(cc_paths));
			return;
		}

		jobs = std::min(jobs, GetSize(work));
		log("Compiling %d evaluator(s) with %d concurrent job(s).\n", GetSize(work), jobs);
		for (auto &cc_path : work)
			log("  %s\n", cxxrtl_compile_command(cc_path).c_str());
		log_flush();

		// Worker threads only spawn compiler processes and record exit codes.
		std::atomic<size_t> next(0);
		std::vector<int> results(work.size(), -1);
		auto worker = [&]() {
			while (true) {
				size_t i = next.fetch_add(1);
				if (i >= work.size())
					return;
				results[i] = run_command(cxxrtl_compile_command(work[i]));
			}
		};

		std::vector<std::thread> threads;
		for (int i = 0; i < jobs; i++)
			threads.emplace_back(worker);
		for (auto &t : threads)
			t.join();

		int failed = 0;
		for (size_t i = 0; i < work.size(); i++) {
			if (results[i] != 0) {
				log("Compilation FAILED (exit %d): %s\n", results[i], work[i].c_str());
				failed++;
			}
		}
		// If any fail, we can't continue
		if (failed > 0)
			log_cmd_error("%d of %d evaluator compilation(s) failed.\n", failed, GetSize(work));
		log("Compiled %d evaluator(s).\n", GetSize(work));
		log_flush();
	}
} CxxrtlCompilePass;

PRIVATE_NAMESPACE_END
