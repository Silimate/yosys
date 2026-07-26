/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Silimate
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
#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"
#include "kernel/ff.h"
#include "kernel/newcelltypes.h"

#include <chrono>
#include <cstdlib>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>

#ifndef _WIN32
#  include <sys/stat.h>
#  include <unistd.h>
#endif

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

enum class KeplerMode {
	Lec,
	Sec,
	Auto
};

static bool is_seq_cell(const RTLIL::Cell *cell)
{
	return StaticCellTypes::categories.is_ff(cell->type);
}

static pool<IdString> sequential_cell_names(RTLIL::Module *mod)
{
	pool<IdString> names;
	for (auto cell : mod->cells())
		if (is_seq_cell(cell))
			names.insert(cell->name);
	return names;
}

static bool sequential_names_match(RTLIL::Module *gold, RTLIL::Module *gate)
{
	return sequential_cell_names(gold) == sequential_cell_names(gate);
}

static std::string shell_quote(const std::string &s)
{
	std::string out = "'";
	for (char c : s) {
		if (c == '\'')
			out += "'\\''";
		else
			out += c;
	}
	out += "'";
	return out;
}

static bool file_exists(const std::string &path)
{
	std::ifstream f(path);
	return f.good();
}

static std::string find_kepler_exe(RTLIL::Design *design, const std::string &cli_exe)
{
	if (!cli_exe.empty())
		return cli_exe;

	std::string from_pad = design->scratchpad_get_string("kepler_lec.exe", "");
	if (!from_pad.empty())
		return from_pad;

	const char *env_exe = getenv("KEPLER_FORMAL_EXE");
	if (env_exe != nullptr && env_exe[0] != '\0')
		return std::string(env_exe);

	return "kepler-formal";
}

static std::string find_primitives_path(RTLIL::Design *design)
{
	std::string from_pad = design->scratchpad_get_string("kepler_lec.primitives", "");
	if (!from_pad.empty() && file_exists(from_pad))
		return from_pad;

	const char *env_prim = getenv("KEPLER_LEC_PRIMITIVES");
	if (env_prim != nullptr && env_prim[0] != '\0' && file_exists(env_prim))
		return std::string(env_prim);

	std::string share = proc_share_dirname() + "silimate/kepler/yosys_primitives.py";
	if (file_exists(share))
		return share;

	return share;
}

static void write_yaml_config(const std::string &path, const std::string &mode,
		const std::string &gold_v, const std::string &gate_v,
		const std::string &primitives, const std::string &log_file,
		const std::string &result_json, const std::string &sec_engine, int max_k,
		bool exit_nonzero_on_diff)
{
	std::ofstream out(path);
	if (!out)
		log_error("kepler_lec: failed to write config %s\n", path.c_str());

	out << "format: verilog\n";
	out << "verification: " << mode << "\n";
	out << "input_paths:\n";
	out << "  - " << gold_v << "\n";
	out << "  - " << gate_v << "\n";
	out << "py_tech_files:\n";
	out << "  - " << primitives << "\n";
	out << "log_file: " << log_file << "\n";
	out << "compact_mode: true\n";
	out << "result_json: " << result_json << "\n";
	if (exit_nonzero_on_diff)
		out << "exit_nonzero_on_diff: true\n";
	if (mode == "sec") {
		out << "sec_engine: " << sec_engine << "\n";
		out << "max_k: " << max_k << "\n";
		out << "sec_encoding: dual_rail_steady\n";
	}
}

struct KeplerResult {
	std::string verdict = "error";
	std::string mode;
	std::string engine;
	int k = -1;
	double runtime_s = 0.0;
};

static bool parse_result_json(const std::string &path, KeplerResult &result)
{
	std::ifstream in(path);
	if (!in)
		return false;
	std::stringstream buffer;
	buffer << in.rdbuf();
	std::string text = buffer.str();

	auto extract_string = [&](const char *key) -> std::string {
		std::string needle = std::string("\"") + key + "\"";
		auto pos = text.find(needle);
		if (pos == std::string::npos)
			return "";
		pos = text.find(':', pos);
		if (pos == std::string::npos)
			return "";
		pos = text.find('"', pos);
		if (pos == std::string::npos)
			return "";
		auto end = text.find('"', pos + 1);
		if (end == std::string::npos)
			return "";
		return text.substr(pos + 1, end - pos - 1);
	};
	auto extract_number = [&](const char *key) -> double {
		std::string needle = std::string("\"") + key + "\"";
		auto pos = text.find(needle);
		if (pos == std::string::npos)
			return 0.0;
		pos = text.find(':', pos);
		if (pos == std::string::npos)
			return 0.0;
		pos++;
		while (pos < text.size() && (text[pos] == ' ' || text[pos] == '\t'))
			pos++;
		return atof(text.c_str() + pos);
	};

	result.verdict = extract_string("verdict");
	result.mode = extract_string("mode");
	result.engine = extract_string("engine");
	result.k = (int)extract_number("k");
	result.runtime_s = extract_number("runtime_s");
	return !result.verdict.empty();
}

static bool parse_result_from_log(const std::string &path, KeplerResult &result)
{
	std::ifstream in(path);
	if (!in)
		return false;
	std::string line;
	while (std::getline(in, line)) {
		if (line.find("No difference was found") != std::string::npos) {
			result.verdict = "equivalent";
			auto kpos = line.find("k = ");
			if (kpos != std::string::npos)
				result.k = atoi(line.c_str() + kpos + 4);
		} else if (line.find("Difference was found") != std::string::npos) {
			result.verdict = "different";
			auto kpos = line.find("k = ");
			if (kpos != std::string::npos)
				result.k = atoi(line.c_str() + kpos + 4);
		} else if (line.find("was inconclusive") != std::string::npos) {
			result.verdict = "inconclusive";
		}
	}
	return result.verdict != "error";
}

static void normalize_and_write(RTLIL::Design *parent, RTLIL::Module *mod,
		const std::string &role, const std::string &out_v, bool use_autoname)
{
	RTLIL::Design scratch;
	RTLIL::Module *copy = mod->clone();
	scratch.add(copy);

	Pass::call(&scratch, "hierarchy -top " + RTLIL::unescape_id(copy->name));
	Pass::call(&scratch, "flatten");
	Pass::call(&scratch, "async2sync");
	Pass::call(&scratch, "dffunmap");
	Pass::call(&scratch, "ffnormpol");
	Pass::call(&scratch, "zinit");
	Pass::call(&scratch, "setundef -zero -undriven -init");
	Pass::call(&scratch, "techmap");
	Pass::call(&scratch, "simplemap");
	Pass::call(&scratch, "aigmap");
	Pass::call(&scratch, "opt_clean -purge");
	if (use_autoname)
		Pass::call(&scratch, "autoname");

	Backend::backend_call(&scratch, nullptr, out_v, "verilog -noattr -noexpr -simple-lhs");
	log("kepler_lec: wrote %s netlist to %s\n", role.c_str(), out_v.c_str());
	(void)parent;
}

struct KeplerLecPass : public Pass {
	KeplerLecPass() : Pass("kepler_lec", "prove gold/gate equivalence with kepler-formal") {}

	void help() override
	{
		log("\n");
		log("    kepler_lec [options] <gold_module> <gate_module>\n");
		log("\n");
		log("Export gate-level Verilog for the named gold and gate modules and prove\n");
		log("combinational (LEC) or sequential (SEC) equivalence with kepler-formal.\n");
		log("\n");
		log("    -mode lec|sec|auto\n");
		log("        Verification mode. 'auto' (default) uses LEC when sequential cell\n");
		log("        instance names match across gold/gate, otherwise SEC.\n");
		log("\n");
		log("    -sec-engine pdr|imc|k_induction\n");
		log("        SEC proof engine (default: pdr).\n");
		log("\n");
		log("    -k <N>\n");
		log("        SEC max proof bound (default: 32).\n");
		log("\n");
		log("    -exe <path>\n");
		log("        Path to the kepler-formal binary. Also accepted via scratchpad\n");
		log("        kepler_lec.exe or the KEPLER_FORMAL_EXE environment variable.\n");
		log("\n");
		log("    -timeout <sec>\n");
		log("        Kill the kepler-formal child after <sec> seconds (uses timeout/\n");
		log("        gtimeout when available).\n");
		log("\n");
		log("    -tmpdir <dir>\n");
		log("        Use an existing directory for intermediate files.\n");
		log("\n");
		log("    -nocleanup\n");
		log("        Keep the temporary working directory.\n");
		log("\n");
		log("    -assert\n");
		log("        Abort with an error if the designs are not proven equivalent.\n");
		log("\n");
		log("Results are written to the design scratchpad:\n");
		log("    kepler_lec.result      equivalent|different|inconclusive|error\n");
		log("    kepler_lec.mode        lec|sec\n");
		log("    kepler_lec.runtime_s   wall-clock seconds\n");
		log("    kepler_lec.k           SEC proof bound when applicable\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing KEPLER_LEC pass (kepler-formal equivalence).\n");

		KeplerMode mode = KeplerMode::Auto;
		std::string sec_engine = "pdr";
		int max_k = 32;
		std::string exe_override;
		int timeout_s = 0;
		std::string tmpdir_override;
		bool cleanup = true;
		bool do_assert = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-mode" && argidx + 1 < args.size()) {
				std::string m = args[++argidx];
				if (m == "lec")
					mode = KeplerMode::Lec;
				else if (m == "sec")
					mode = KeplerMode::Sec;
				else if (m == "auto")
					mode = KeplerMode::Auto;
				else
					log_cmd_error("kepler_lec: invalid -mode '%s'\n", m.c_str());
				continue;
			}
			if (args[argidx] == "-sec-engine" && argidx + 1 < args.size()) {
				sec_engine = args[++argidx];
				if (sec_engine != "pdr" && sec_engine != "imc" && sec_engine != "k_induction")
					log_cmd_error("kepler_lec: invalid -sec-engine '%s'\n", sec_engine.c_str());
				continue;
			}
			if (args[argidx] == "-k" && argidx + 1 < args.size()) {
				max_k = atoi(args[++argidx].c_str());
				if (max_k < 0)
					log_cmd_error("kepler_lec: -k must be non-negative\n");
				continue;
			}
			if (args[argidx] == "-exe" && argidx + 1 < args.size()) {
				exe_override = args[++argidx];
				continue;
			}
			if (args[argidx] == "-timeout" && argidx + 1 < args.size()) {
				timeout_s = atoi(args[++argidx].c_str());
				if (timeout_s < 0)
					log_cmd_error("kepler_lec: -timeout must be non-negative\n");
				continue;
			}
			if (args[argidx] == "-tmpdir" && argidx + 1 < args.size()) {
				tmpdir_override = args[++argidx];
				continue;
			}
			if (args[argidx] == "-nocleanup") {
				cleanup = false;
				continue;
			}
			if (args[argidx] == "-assert") {
				do_assert = true;
				continue;
			}
			break;
		}

		if (argidx + 2 != args.size())
			log_cmd_error("kepler_lec: expected <gold_module> <gate_module>\n");

		IdString gold_id = RTLIL::escape_id(args[argidx]);
		IdString gate_id = RTLIL::escape_id(args[argidx + 1]);
		RTLIL::Module *gold_mod = design->module(gold_id);
		RTLIL::Module *gate_mod = design->module(gate_id);
		if (gold_mod == nullptr)
			log_cmd_error("kepler_lec: gold module %s not found\n", log_id(gold_id));
		if (gate_mod == nullptr)
			log_cmd_error("kepler_lec: gate module %s not found\n", log_id(gate_id));

		std::string resolved_mode;
		if (mode == KeplerMode::Lec)
			resolved_mode = "lec";
		else if (mode == KeplerMode::Sec)
			resolved_mode = "sec";
		else {
			bool match = sequential_names_match(gold_mod, gate_mod);
			resolved_mode = match ? "lec" : "sec";
			log("kepler_lec: auto mode selected %s (sequential instance names %s)\n",
					resolved_mode.c_str(), match ? "match" : "differ");
		}

		std::string tmpdir;
		bool own_tmpdir = false;
		if (!tmpdir_override.empty()) {
			tmpdir = tmpdir_override;
			// Ensure the caller-provided directory exists.
#ifdef _WIN32
			_mkdir(tmpdir.c_str());
#else
			mkdir(tmpdir.c_str(), 0777);
#endif
		} else {
			tmpdir = make_temp_dir(get_base_tmpdir() + "/yosys-kepler-XXXXXX");
			own_tmpdir = true;
		}

		// Always resolve to an absolute path so YAML entries remain valid after
		// we `cd` into the working directory to run kepler-formal.
		{
			char *resolved = realpath(tmpdir.c_str(), nullptr);
			if (resolved != nullptr) {
				tmpdir = resolved;
				free(resolved);
			}
		}

		std::string gold_v = tmpdir + "/gold.v";
		std::string gate_v = tmpdir + "/gate.v";
		std::string cfg = tmpdir + "/kepler.yaml";
		std::string log_file = tmpdir + "/kepler.log";
		std::string result_json = tmpdir + "/result.json";
		std::string primitives = find_primitives_path(design);

		if (!file_exists(primitives))
			log_error("kepler_lec: primitives file not found: %s\n", primitives.c_str());

		bool use_autoname = (resolved_mode == "sec");
		normalize_and_write(design, gold_mod, "gold", gold_v, use_autoname);
		normalize_and_write(design, gate_mod, "gate", gate_v, use_autoname);

		write_yaml_config(cfg, resolved_mode, gold_v, gate_v, primitives, log_file,
				result_json, sec_engine, max_k, /*exit_nonzero_on_diff=*/false);

		std::string exe = find_kepler_exe(design, exe_override);
		std::string cmd = shell_quote(exe) + " --config " + shell_quote(cfg);

		if (timeout_s > 0) {
			// Prefer GNU timeout / Homebrew gtimeout when present.
			if (system("command -v gtimeout >/dev/null 2>&1") == 0)
				cmd = "gtimeout " + std::to_string(timeout_s) + " " + cmd;
			else if (system("command -v timeout >/dev/null 2>&1") == 0)
				cmd = "timeout " + std::to_string(timeout_s) + " " + cmd;
			else
				log_warning("kepler_lec: -timeout requested but neither timeout nor "
						"gtimeout is available; running without a wall-clock limit.\n");
		}

		const char *py_extra = getenv("KEPLER_FORMAL_PYTHONPATH");
		if (py_extra == nullptr || py_extra[0] == '\0')
			py_extra = getenv("PYTHONPATH");
		std::string env_prefix;
		if (py_extra != nullptr && py_extra[0] != '\0')
			env_prefix = "PYTHONPATH=" + shell_quote(py_extra) + " ";

		cmd = "cd " + shell_quote(tmpdir) + " && " + env_prefix + cmd + " 2>&1";
		log("kepler_lec: running %s\n", cmd.c_str());

		auto t0 = std::chrono::steady_clock::now();
		std::string captured;
		int rc = run_command(cmd, [&](const std::string &line) {
			captured += line;
			captured += "\n";
			log("kepler-formal | %s\n", line.c_str());
		});
		auto t1 = std::chrono::steady_clock::now();
		double wall_s = std::chrono::duration<double>(t1 - t0).count();

		KeplerResult result;
		result.mode = resolved_mode;
		result.engine = (resolved_mode == "sec") ? sec_engine : "miter";
		result.runtime_s = wall_s;

		bool parsed = parse_result_json(result_json, result);
		if (!parsed)
			parsed = parse_result_from_log(log_file, result);
		if (!parsed) {
			if (rc == 124 || rc == 143)
				result.verdict = "inconclusive";
			else if (rc != 0)
				result.verdict = "error";
			else
				result.verdict = "error";
		}
		if (result.runtime_s <= 0.0)
			result.runtime_s = wall_s;

		design->scratchpad_set_string("kepler_lec.result", result.verdict);
		design->scratchpad_set_string("kepler_lec.mode", result.mode);
		design->scratchpad_set_string("kepler_lec.engine", result.engine);
		design->scratchpad_set_string("kepler_lec.runtime_s", std::to_string(result.runtime_s));
		design->scratchpad_set_int("kepler_lec.k", result.k);
		design->scratchpad_set_string("kepler_lec.tmpdir", tmpdir);
		design->scratchpad_set_string("kepler_lec.log", log_file);
		design->scratchpad_set_string("kepler_lec.result_json", result_json);

		log("kepler_lec: verdict=%s mode=%s runtime=%.3fs k=%d rc=%d\n",
				result.verdict.c_str(), result.mode.c_str(), result.runtime_s,
				result.k, rc);

		if (own_tmpdir && cleanup && result.verdict == "equivalent")
			remove_directory(tmpdir);
		else if (own_tmpdir && cleanup)
			log("kepler_lec: keeping tempdir %s (verdict=%s)\n",
					tmpdir.c_str(), result.verdict.c_str());

		if (do_assert && result.verdict != "equivalent")
			log_error("kepler_lec: designs are not equivalent (verdict=%s)\n",
					result.verdict.c_str());
	}
} KeplerLecPass;

PRIVATE_NAMESPACE_END
