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

#ifndef CXXRTL_SIM_H
#define CXXRTL_SIM_H

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

// Location of the CXXRTL runtime headers shipped in yosys's share directory.
inline std::string cxxrtl_runtime_dir()
{
	std::string runtime_dir = proc_share_dirname() + "include/backends/cxxrtl/runtime";
	if (!check_file_exists(runtime_dir + "/cxxrtl/cxxrtl.h"))
		log_cmd_error("CXXRTL runtime headers not found at %s.\n", runtime_dir.c_str());
	return runtime_dir;
}

// Path of the shared object compiled from a write_cxxrtl output file.
inline std::string cxxrtl_so_path(const std::string &cc_path)
{
	return cc_path.substr(0, cc_path.size() - 3) + ".so";
}

// Shell command compiling a write_cxxrtl output file into a self-contained
// evaluator .so (the CXXRTL C API implementation is compiled in).
inline std::string cxxrtl_compile_command(const std::string &cc_path)
{
	const char *cxx = getenv("CXX");
	if (cxx == nullptr || cxx[0] == 0)
		cxx = "c++";
	return stringf("%s -O2 -std=c++14 -fPIC -shared -DCXXRTL_INCLUDE_CAPI_IMPL "
	               "-I %s -o %s %s",
	               cxx, cxxrtl_runtime_dir().c_str(),
	               cxxrtl_so_path(cc_path).c_str(), cc_path.c_str());
}

// True when the .so for cc_path exists and is at least as new as the .cc.
inline bool cxxrtl_so_up_to_date(const std::string &cc_path)
{
	struct stat st_cc, st_so;
	if (stat(cc_path.c_str(), &st_cc) != 0)
		return false;
	if (stat(cxxrtl_so_path(cc_path).c_str(), &st_so) != 0)
		return false;
	return st_so.st_mtime >= st_cc.st_mtime;
}

YOSYS_NAMESPACE_END

#endif
