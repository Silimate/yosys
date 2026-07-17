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
#include "kernel/fstdata.h"
#include "backends/cxxrtl/runtime/cxxrtl/capi/cxxrtl_capi.h"

#include <cmath>
#include <deque>
#include <dlfcn.h>
#include <fstream>
#include <iomanip>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Time string exponent converter.
static const std::map<std::string, int> g_units =
{
	{ "",    -9 }, // default is ns
	{ "s",    0 },
	{ "ms",  -3 },
	{ "us",  -6 },
	{ "ns",  -9 },
	{ "ps", -12 },
	{ "fs", -15 },
	{ "as", -18 },
	{ "zs", -21 },
};

static double stringToTime(std::string str)
{
	if (str == "END") return -1;

	char *endptr;
	long value = strtol(str.c_str(), &endptr, 10);

	if (g_units.find(endptr) == g_units.end())
		log_error("Cannot parse '%s', bad unit '%s'\n", str.c_str(), endptr);

	if (value < 0)
		log_error("Time value '%s' must be positive\n", str.c_str());

	return value * pow(10.0, g_units.at(endptr));
}

// Format a CXXRTL object's current value as an MSB-first binary string (debug -vcd dump).
static std::string value_to_bits(const struct cxxrtl_object *object)
{
	std::string s;
	s.reserve(object->width);
	for (int bit = (int)object->width - 1; bit >= 0; bit--)
		s += ((object->curr[bit / 32] >> (bit % 32)) & 1) ? '1' : '0';
	return s;
}

// Generate a printable VCD identifier code (base-94, ASCII 33..126) for signal index n.
static std::string vcd_ident(size_t n)
{
	std::string s;
	do {
		s += char(33 + (n % 94));
		n /= 94;
	} while (n > 0);
	return s;
}

// Function pointer types for the C API symbols resolved from the evaluator.
// The C API implementation is compiled into the evaluator itself (-DCXXRTL_INCLUDE_CAPI_IMPL).
typedef cxxrtl_toplevel (*fn_create_design)();                     // build design object in C++
typedef cxxrtl_handle (*fn_create_handle)(cxxrtl_toplevel);        // wrap design in runnable handle
typedef void (*fn_destroy_handle)(cxxrtl_handle);                  // tear down design
typedef size_t (*fn_step)(cxxrtl_handle);                          // simulate the circuit to a fixed point
typedef void (*fn_enum_signals)(cxxrtl_handle, void *,             // walk over every visible signal ($var)
	void (*)(void *, const char *, struct cxxrtl_object *, size_t));
typedef void (*fn_eval_outline)(cxxrtl_outline);                   // recompute OUTLINE signal values (optimized nets)

// Switching activity measured once for each unique CXXRTL curr buffer.
struct SignalActivity {
	uint32_t *curr;                      // shared CXXRTL value storage
	size_t width;                        // number of signal bits
	std::vector<uint32_t> prev;          // previous sample value
	std::vector<double> toggle_counts;   // per-bit toggle counts
	std::vector<uint64_t> high_times;    // per-bit accumulated high time
	std::vector<uint64_t> last_change;   // per-bit time of last observed change
};

// One named signal/port/register of the design.
struct DesignSignal {
	std::string name;         // hierarchical name from CXXRTL (space/dot separated)
	Wire *wire;               // matching wire in the design, or nullptr
	struct cxxrtl_object *object; // this name's descriptor, used when driving it
	SignalActivity *activity; // counters this net uses (shared by aliased names)
	fstHandle fst_handle;     // matching FST waveform signal, or 0
};

// One net reported by the evaluator, before we build the tables.
struct RawSignal {
	const char *name;
	struct cxxrtl_object *object;
};

// One CXXRTL memory restored from the waveform at the first sample.
struct DesignMemory {
	std::string name;
	struct cxxrtl_object *object;
	dict<int, fstHandle> fst_handles;
};

// Signals and memories discovered in one CXXRTL enumeration.
struct EnumeratedObjects {
	std::vector<RawSignal> signals;
	std::vector<DesignMemory> memories;
};

struct CxxrtlSimPass : public Pass {
	CxxrtlSimPass() : Pass("cxxrtl_sim", "re-simulate with a CXXRTL evaluator and annotate activity") {}

	void help() override
	{
		log("\n");
		log("    cxxrtl_sim -so <file.so> -r <waveform> [options]\n");
		log("\n");
		log("Load a compiled CXXRTL evaluator emitted by write_cxxrtl, replay an input waveform through it,\n");
		log("and annotate per-bit $ACKT/$DUTY activity onto the wires of the current design \n");
		log("\n");
		log("    -so <file.so>\n");
		log("        precompiled evaluator.\n");
		log("\n");
		log("    -module <name>\n");
		log("        the design module the evaluator was emitted from.\n");
		log("\n");
		log("    -instance <cell>=<module>:<scope>\n");
		log("    -instance <module>:<scope>\n");
		log("        cut mode: map a wrapper cell (or module-named cell) in a fused\n");
		log("        evaluator to a design module and FST scope. Repeat once per\n");
		log("        batch member. Incompatible with -module/-scope.\n");
		log("\n");
		log("    -r <file.fst|file.vcd>\n");
		log("        input waveform; VCD is converted via vcd2fst (required).\n");
		log("        x/z stimulus bits are normalized to 0.\n");
		log("\n");
		log("    -scope <name>\n");
		log("        scope within the file to query from for the given module/evaluator.\n");
		log("\n");
		log("    -clk-period <seconds>\n");
		log("        master clock period override (normally supplied by the runner).\n");
		log("        Otherwise, derives from the fastest-toggling signal and\n");
		log("        assumes it's clock period from the timescale of the waveform.\n");
		log("\n");
		log("    -start <time>, -stop <time>\n");
		log("        replay window; bare numbers are ns, unit suffixes (us/ns/ps/...)\n");
		log("        and END are accepted, like the sim pass (default: full range).\n");
		log("\n");
		log("    -reg\n");
		log("        overwrite register states from the waveform every sample.\n");
		log("\n");
		log("    -fast\n");
		log("        filtered waveform replay: only decompress primary inputs plus\n");
		log("        registers/memories (for init; mid-run overwrite only with -reg).\n");
		log("\n");
		log("    -log-interval <n>\n");
		log("        log progress every <n> samples.\n");
		log("\n");
		log("    -vcd <file>\n");
		log("        dump per-sample settled signal values to <file> in VCD format\n");
		log("        (debug; lets you diff the replay against the sim pass waveform).\n");
		log("\n");
		log("    -d\n");
		log("        enable debug output.\n");
		log("\n");
	}

	// Resolve a CXXRTL signal name to a wire of the hierarchical design.
	static Wire *resolve_wire(Design *design, Module *mod, std::string name)
	{
		for (auto &c : name)
			if (c == ' ') // CXXRTL signal names uses spaces as hierarchy separators
				c = '.';
		// Traverse hierarchy to find the wire. in the design.
		while (true) {
			// Check if current module has a wire with this name.
			if (Wire *w = mod->wire(RTLIL::escape_id(name)))
				return w;
			// Otherwise, check if the current module has a cell with the first part of the name.
			size_t dot = name.find('.');
			if (dot == std::string::npos)
				return nullptr;
			Cell *cell = mod->cell(RTLIL::escape_id(name.substr(0, dot)));
			if (cell == nullptr)
				return nullptr;
			// Find the module that contains the cell and continue.
			mod = design->module(cell->type);
			if (mod == nullptr)
				return nullptr;
			name = name.substr(dot + 1);
		}
	}

	// Turn a CXXRTL name into the corresponding FST name that can be looked up in the waveform.
	static std::string waveform_name(const std::string &scope, std::string name)
	{
		name = scope + "." + name;
		for (auto &c : name)
			if (c == ' ')
				c = '.';
		return name;
	}

	// Keep ordinary signals for activity and memories for first-sample restoration.
	static void keep_object(void *context, const char *name, struct cxxrtl_object *object, size_t parts)
	{
		if (parts != 1)
			return; // multi-part objects unsupported (post-splitnets)

		auto &objects = *static_cast<EnumeratedObjects*>(context);
		if (object->type == CXXRTL_MEMORY) {
			if (object->width > 0 && object->depth > 0)
				objects.memories.push_back({ name, object, {} });
			return;
		}

		if (object->depth == 1 && object->width > 0)
			objects.signals.push_back({ name, object });
	}

	// Finds or creates a SignalActivity object for a DesignSignal object.
	SignalActivity *find_or_add_activity(
		struct cxxrtl_object *object,
		std::deque<SignalActivity> &activities,
		dict<uintptr_t, SignalActivity*> &seen
	) {
		// CXXRTL storage address identifies the net, which can be common between multiple signals (same wire connection)
		uintptr_t key = (uintptr_t)object->curr;
		auto it = seen.find(key);
		if (it != seen.end())
			return it->second; // same storage address -> reuse the same activity object

		// Otherwise, create a new activity object, mapping the storage address to it for later reuse.
		activities.emplace_back();
		SignalActivity &act = activities.back();
		act.curr = object->curr;
		act.width = object->width;
		act.prev.assign((object->width + 31) / 32, 0);
		act.toggle_counts.assign(object->width, 0.0);
		act.high_times.assign(object->width, 0);
		act.last_change.assign(object->width, 0);
		seen[key] = &act;
		return &act;
	}

	// Write an FST value (MSB first; x/z mapped to 0) into packed 32-bit representation expected by CXXRTL.
	static bool write_value(uint32_t *target, size_t width, const std::string &value)
	{
		size_t num_words = (width + 31) / 32; // number of words needed to represent the 'width' bits including padding
		bool changed = false;
		size_t nbits = std::min(value.size(), width);
		for (size_t word = 0; word < num_words; word++) {
			uint32_t packed = 0;
			size_t first_bit = word * 32; // LSB of the current word
			size_t last_bit = std::min(first_bit + 32, nbits); // MSB of the current word
			for (size_t bit = first_bit; bit < last_bit; bit++)
				if (value[value.size() - 1 - bit] == '1') // convert the FST value to a 32-bit packed representation
					packed |= (uint32_t)1 << (bit - first_bit);
			if (target[word] != packed)
				changed = true;
			target[word] = packed; // example: target[0] = bits 0-31, target[1] = bits 32-63, etc.
		}
		return changed;
	}

	// Write an FST value into a CXXRTL object and report whether it changed.
	static bool write_object(struct cxxrtl_object *object, const std::string &value)
	{
		uint32_t *target = object->next != nullptr ? object->next : object->curr;
		bool changed = write_value(target, object->width, value);
		// Initialization and register restoration must be immediately visible.
		if (object->next != nullptr && object->next != object->curr)
			changed |= write_value(object->curr, object->width, value);
		return changed;
	}

	// Apply current FST values and report whether any CXXRTL object changed.
	static bool apply_waveform(FstData &fst, const std::vector<DesignSignal*> &signals)
	{
		bool changed = false;
		for (auto *sig : signals) {
			std::string value = fst.valueOf(sig->fst_handle);
			changed |= write_object(sig->object, value);
		}
		return changed;
	}

	// Restore every available FST memory row before the first simulation step.
	static void initialize_memories(FstData &fst, const std::vector<DesignMemory> &memories)
	{
		for (auto &memory : memories) {
			auto *object = memory.object;
			size_t words_per_row = (object->width + 31) / 32;
			for (auto &row_handle : memory.fst_handles) {
				if (row_handle.first < 0)
					continue;
				size_t row = row_handle.first;
				if (row < object->zero_at || row >= object->zero_at + object->depth)
					continue;
				uint32_t *target = object->curr + (row - object->zero_at) * words_per_row;
				write_value(target, object->width, fst.valueOf(row_handle.second));
			}
		}
	}

	// Recompute optimized-away combinational nets before observing them.
	static void refresh_outlines(const pool<cxxrtl_outline> &outlines,
	                             fn_eval_outline eval_outline)
	{
		for (auto outline : outlines)
			eval_outline(outline);
	}

	// Capture the first stable state without recording an artificial toggle.
	static void initialize_activity(std::deque<SignalActivity> &activities)
	{
		for (auto &act : activities)
			for (size_t word = 0; word < act.prev.size(); word++)
				act.prev[word] = act.curr[word];
	}

	// Compare the new stable state with the preceding sample.
	static void measure_activity(std::deque<SignalActivity> &activities, uint64_t time)
	{
		for (auto &act : activities) {
			for (size_t word = 0; word < act.prev.size(); word++) {
				const uint32_t *curr = act.curr;
				uint32_t diff = curr[word] ^ act.prev[word];
				while (diff != 0) {
					int word_bit = __builtin_ctz(diff);
					diff &= diff - 1;
					size_t bit = word * 32 + word_bit;
					if (bit >= act.width)
						break;
					if ((act.prev[word] >> word_bit) & 1)
						act.high_times[bit] += time - act.last_change[bit];
					act.last_change[bit] = time;
					act.toggle_counts[bit] += 1.0;
				}
				act.prev[word] = curr[word];
			}
		}
	}

	// Split a fused-cut CXXRTL name into wrapper cell (`c0`) + signal remainder.
	// write_cxxrtl_cut_evaluator names wrapper ports `cN.port` (dot in the
	// IdString), which CXXRTL exposes as flat `cN.port` — not `cN port`.
	// Also accept space-separated hierarchy from true cell-internal signals.
	static bool split_cell_prefix(const std::string &name, std::string &cell, std::string &rest)
	{
		size_t sp = name.find(' ');
		if (sp != std::string::npos) {
			cell = name.substr(0, sp);
			rest = name.substr(sp + 1);
			return true;
		}
		// Flat wrapper port: c12.clock / c12.io_q / c12.child.port
		if (name.size() >= 3 && name[0] == 'c' && isdigit((unsigned char)name[1])) {
			size_t i = 1;
			while (i < name.size() && isdigit((unsigned char)name[i]))
				i++;
			if (i < name.size() && name[i] == '.') {
				cell = name.substr(0, i);
				rest = name.substr(i + 1);
				return true;
			}
		}
		cell = name;
		rest.clear();
		return false;
	}

	void collect_signals(
		// CXXRTL knobs
		cxxrtl_handle handle,
		fn_enum_signals enum_signals,

		// Yosys design
		Design *design,
		Module *top,

		// Output tables
		std::vector<DesignSignal> &signals,
		std::deque<SignalActivity> &activities,
		std::vector<DesignMemory> &memories
	) {
		EnumeratedObjects objects;
		enum_signals(handle, &objects, keep_object);
		memories = std::move(objects.memories);

		// Map storage address to its corresponding activity object.
		dict<uintptr_t, SignalActivity*> seen;

		// For every net, create a DesignSignal object and store it into the signal table.
		for (auto &r : objects.signals) {
			DesignSignal sig;
			sig.name = r.name;
			sig.wire = resolve_wire(design, top, sig.name);
			sig.object = r.object;
			sig.fst_handle = 0;
			sig.activity = find_or_add_activity(r.object, activities, seen);
			signals.push_back(std::move(sig));
		}
	}

	// Like collect_signals, but each CXXRTL name is rooted at a wrapper cell
	// (`c0 foo`) mapped to a design module via -instance.
	void collect_signals_cut(
		cxxrtl_handle handle,
		fn_enum_signals enum_signals,
		Design *design,
		const dict<std::string, Module*> &cell_to_module,
		std::vector<DesignSignal> &signals,
		std::deque<SignalActivity> &activities,
		std::vector<DesignMemory> &memories
	) {
		EnumeratedObjects objects;
		enum_signals(handle, &objects, keep_object);
		memories = std::move(objects.memories);

		dict<uintptr_t, SignalActivity*> seen;
		for (auto &r : objects.signals) {
			DesignSignal sig;
			sig.name = r.name;
			sig.object = r.object;
			sig.fst_handle = 0;
			sig.activity = find_or_add_activity(r.object, activities, seen);
			sig.wire = nullptr;

			std::string cell, rest;
			split_cell_prefix(sig.name, cell, rest);
			auto it = cell_to_module.find(cell);
			if (it != cell_to_module.end() && !rest.empty())
				sig.wire = resolve_wire(design, it->second, rest);
			signals.push_back(std::move(sig));
		}
	}

	// Pass entry point
	void execute(std::vector<std::string> args, Design *design) override
	{
		log_header(design, "Executing CXXRTL_SIM pass (FST-driven CXXRTL re-simulation).\n");

		// Initialize variable defaults
		std::string so_path, wave_path, scope, module_name, vcd_path;
		// cut mode: wrapper cell -> (design module name, FST scope)
		std::vector<std::tuple<std::string, std::string, std::string>> instances;
		double clk_period_override = 0;
		double start_time = 0, stop_time = -1;
		int log_interval = 0;
		bool reg_overwrite = false;
		bool fast = false;
		bool debug = false;

		// Argument parsing
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-so" && argidx+1 < args.size()) {
				so_path = args[++argidx];
				continue;
			}
			if (args[argidx] == "-module" && argidx+1 < args.size()) {
				module_name = args[++argidx];
				continue;
			}
			if (args[argidx] == "-instance" && argidx+1 < args.size()) {
				std::string spec = args[++argidx];
				std::string cell, mod, inst_scope;
				size_t eq = spec.find('=');
				std::string rest = spec;
				if (eq != std::string::npos) {
					cell = spec.substr(0, eq);
					rest = spec.substr(eq + 1);
				}
				size_t colon = rest.find(':');
				if (colon == std::string::npos)
					log_cmd_error("Invalid -instance '%s'; expected [cell=]module:scope.\n",
					              spec.c_str());
				mod = rest.substr(0, colon);
				inst_scope = rest.substr(colon + 1);
				if (cell.empty())
					cell = mod;
				if (cell.empty() || mod.empty() || inst_scope.empty())
					log_cmd_error("Invalid -instance '%s'; expected [cell=]module:scope.\n",
					              spec.c_str());
				instances.emplace_back(cell, mod, inst_scope);
				continue;
			}
			if (args[argidx] == "-r" && argidx+1 < args.size()) {
				wave_path = args[++argidx];
				continue;
			}
			if (args[argidx] == "-scope" && argidx+1 < args.size()) {
				scope = args[++argidx];
				continue;
			}
			if (args[argidx] == "-clk-period" && argidx+1 < args.size()) {
				clk_period_override = atof(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-start" && argidx+1 < args.size()) {
				start_time = stringToTime(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-stop" && argidx+1 < args.size()) {
				stop_time = stringToTime(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-log-interval" && argidx+1 < args.size()) {
				log_interval = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-vcd" && argidx+1 < args.size()) {
				vcd_path = args[++argidx];
				continue;
			}
			if (args[argidx] == "-reg") {
				reg_overwrite = true;
				continue;
			}
			if (args[argidx] == "-fast") {
				fast = true;
				continue;
			}
			if (args[argidx] == "-d") {
				debug = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		// .so and waveform are required
		if (so_path.empty())
			log_cmd_error("-so <file.so> is required.\n");
		if (wave_path.empty())
			log_cmd_error("-r <waveform> is required.\n");

		bool cut_mode = !instances.empty();
		bool module_mode = !module_name.empty();
		if (cut_mode && (module_mode || !scope.empty()))
			log_cmd_error("Cut mode (-instance) cannot be combined with -module/-scope.\n");

		// The annotation root, explicit module or default to top (non-cut mode).
		Module *top = nullptr;
		dict<std::string, Module*> cell_to_module;
		dict<std::string, std::string> cell_to_scope;
		std::vector<Module*> cut_modules;
		if (cut_mode) {
			for (auto &inst : instances) {
				const std::string &cell = std::get<0>(inst);
				const std::string &mod_name = std::get<1>(inst);
				const std::string &inst_scope = std::get<2>(inst);
				Module *mod = design->module(RTLIL::escape_id(mod_name));
				if (mod == nullptr)
					log_cmd_error("Module '%s' not found in design.\n", mod_name.c_str());
				if (cell_to_module.count(cell))
					log_cmd_error("Duplicate -instance cell '%s'.\n", cell.c_str());
				cell_to_module[cell] = mod;
				cell_to_scope[cell] = inst_scope;
				cut_modules.push_back(mod);
				log("Cut instance cell '%s' -> module '%s' scope \"%s\"\n",
				    cell.c_str(), mod_name.c_str(), inst_scope.c_str());
			}
			top = cut_modules.front();
		} else if (module_mode) {
			top = design->module(RTLIL::escape_id(module_name));
			if (top == nullptr)
				log_cmd_error("Module '%s' not found in design.\n", module_name.c_str());
		} else {
			top = design->top_module();
			if (top == nullptr)
				log_cmd_error("No top module found; run `hierarchy -top <module>` first.\n");
		}

		// Load compiled evaluator
		void *so = dlopen(so_path.c_str(), RTLD_NOW | RTLD_LOCAL);
		if (so == nullptr)
			log_cmd_error("dlopen(%s) failed: %s\n", so_path.c_str(), dlerror());
		auto create_design = (fn_create_design)dlsym(so, "cxxrtl_design_create");

		// C API symbols resolved from the evaluator (see typedefs above for more details).
		auto create_handle = (fn_create_handle)dlsym(so, "cxxrtl_create");
		auto destroy_handle = (fn_destroy_handle)dlsym(so, "cxxrtl_destroy");
		auto step = (fn_step)dlsym(so, "cxxrtl_step");
		auto enum_signals = (fn_enum_signals)dlsym(so, "cxxrtl_enum");
		auto eval_outline = (fn_eval_outline)dlsym(so, "cxxrtl_outline_eval");
		if (!create_design || !create_handle || !destroy_handle || !step || !enum_signals ||
		    !eval_outline)
			log_cmd_error("Missing CXXRTL C API symbols in %s.\n", so_path.c_str());

		cxxrtl_handle handle = create_handle(create_design()); // create handle to whole design
		std::vector<DesignSignal> signals;                     // one entry per net name
		std::deque<SignalActivity> activities;                 // one entry per unique storage (shared by aliased names)
		std::vector<DesignMemory> memories;                    // memory state restored at the first sample

		// Populate tables
		if (cut_mode)
			collect_signals_cut(handle, enum_signals, design, cell_to_module,
			                    signals, activities, memories);
		else
			collect_signals(handle, enum_signals, design, top, signals, activities, memories);
		log("Collected %d signals and %d unique wire activities.\n", GetSize(signals), GetSize(activities));

		// Open waveform to drive signals
		FstData fst(wave_path);
		double real_timescale = pow(10.0, fst.getScale());
		if (!cut_mode) {
			if (scope.empty()) {
				scope = fst.autoScope(top);
				if (scope.empty())
					log_cmd_error("No scope found for module '%s'. Please specify -scope.\n",
					              RTLIL::unescape_id(top->name).c_str());
			}
			log("Using scope: \"%s\"\n", scope.c_str());
		}

		int found_inputs = 0, n_inputs = 0;
		int found_regs = 0, n_regs = 0;
		std::vector<DesignSignal*> seed_sigs;
		std::vector<DesignSignal*> input_sigs;
		std::vector<DesignSignal*> reg_sigs;
		pool<cxxrtl_outline> outlines;
		for (auto &sig : signals) {
			// Per-module / cut evaluators expose cut child outputs as additional inputs.
			bool is_input = (sig.object->flags & CXXRTL_INPUT) != 0 &&
			                (module_mode || cut_mode ||
			                 (sig.wire != nullptr && sig.wire->port_input &&
			                  sig.wire->module == top));
			bool is_register = (sig.object->flags & CXXRTL_DRIVEN_SYNC) != 0 &&
			                   sig.object->next != nullptr;
			if (sig.object->type == CXXRTL_OUTLINE && sig.object->outline != nullptr)
				outlines.insert(sig.object->outline);

			std::string fst_name;
			if (cut_mode) {
				std::string cell, rest;
				split_cell_prefix(sig.name, cell, rest);
				auto it = cell_to_scope.find(cell);
				if (it == cell_to_scope.end() || rest.empty())
					fst_name.clear();
				else
					fst_name = waveform_name(it->second, rest);
			} else {
				fst_name = waveform_name(scope, sig.name);
			}
			sig.fst_handle = fst_name.empty() ? 0 : fst.getHandle(fst_name);

			if (is_input) {
				n_inputs++;
				if (sig.fst_handle != 0)
					found_inputs++;
				else
					log_warning("Input port '%s' not found in waveform; left at its initial value.\n",
					            fst_name.empty() ? sig.name.c_str() : fst_name.c_str());
			} else if (reg_overwrite && is_register) {
				n_regs++;
				if (sig.fst_handle != 0)
					found_regs++;
				else if (debug)
					log_warning("Register '%s' not found in waveform; not overwritten.\n",
					            fst_name.empty() ? sig.name.c_str() : fst_name.c_str());
			}

			if (sig.fst_handle == 0)
				continue;
			if (is_input) {
				input_sigs.push_back(&sig);
				seed_sigs.push_back(&sig);
			} else if (is_register) {
				seed_sigs.push_back(&sig);
				if (reg_overwrite)
					reg_sigs.push_back(&sig);
			}
		}
		log("Driving %d/%d input ports from the waveform.\n", found_inputs, n_inputs);
		if (reg_overwrite)
			log("Overwriting %d/%d registers from the waveform.\n", found_regs, n_regs);

		int memory_words = 0, matched_memory_words = 0;
		for (auto &memory : memories) {
			std::string mem_fst;
			if (cut_mode) {
				std::string cell, rest;
				split_cell_prefix(memory.name, cell, rest);
				auto it = cell_to_scope.find(cell);
				if (it != cell_to_scope.end() && !rest.empty())
					mem_fst = waveform_name(it->second, rest);
			} else {
				mem_fst = waveform_name(scope, memory.name);
			}
			if (!mem_fst.empty())
				memory.fst_handles = fst.getMemoryHandles(mem_fst);
			memory_words += memory.object->depth;
			for (auto &row_handle : memory.fst_handles) {
				if (row_handle.first < 0)
					continue;
				size_t row = row_handle.first;
				if (row >= memory.object->zero_at &&
				    row < memory.object->zero_at + memory.object->depth)
					matched_memory_words++;
			}
		}
		if (!memories.empty())
			log("Initializing %d/%d memory words from the waveform.\n",
			    matched_memory_words, memory_words);

		// If no inputs are found, we must error as we cannot drive any signals.
		if (n_inputs > 0 && found_inputs == 0) {
			if (module_mode || cut_mode) {
				log_warning("No input ports matched in the waveform; skipping annotation.\n");
				destroy_handle(handle);
				dlclose(so);
				return;
			}
			log_cmd_error("No input ports matched in the waveform; check -scope.\n");
		}

		// Replay FST on the design
		uint64_t startCount, stopCount;
		if (start_time == 0)
			startCount = fst.getStartTime();
		else if (start_time == -1)
			startCount = fst.getEndTime();
		else
			startCount = std::min((uint64_t)(start_time / real_timescale), fst.getEndTime());
		if (stop_time == 0)
			stopCount = fst.getStartTime();
		else if (stop_time == -1)
			stopCount = fst.getEndTime();
		else
			stopCount = std::min((uint64_t)(stop_time / real_timescale), fst.getEndTime());
		if (stopCount < startCount)
			log_cmd_error("Stop time is before start time.\n");

		bool first_sample = true;
		uint64_t max_time = startCount;
		int sample_count = 0;

		// Optional debug VCD: dump each sample's settled values so the CXXRTL replay
		// can be diffed against the sim pass waveform to localize divergences.
		std::ofstream vcd_file;
		std::vector<std::string> vcd_ids, vcd_prev;
		if (!vcd_path.empty()) {
			// Suffix the module name so per-module invocations (parallel or serial)
			// don't clobber a shared -vcd path: foo.vcd -> foo.<module>.vcd.
			std::string out_path = vcd_path;
			if (!module_name.empty()) {
				size_t dot = out_path.rfind('.');
				std::string base = dot == std::string::npos ? out_path : out_path.substr(0, dot);
				std::string ext = dot == std::string::npos ? ".vcd" : out_path.substr(dot);
				out_path = base + "." + module_name + ext;
			}
			vcd_file.open(out_path.c_str());
			if (!vcd_file.is_open())
				log_cmd_error("Cannot open -vcd file '%s' for writing.\n", out_path.c_str());
			log("Dumping per-sample values to VCD: %s\n", out_path.c_str());
			vcd_file << "$timescale 1" << fst.getTimescaleString() << " $end\n";
			vcd_file << "$scope module cxxrtl $end\n";
			vcd_ids.resize(signals.size());
			vcd_prev.assign(signals.size(), std::string());
			for (size_t i = 0; i < signals.size(); i++) {
				vcd_ids[i] = vcd_ident(i);
				std::string nm = signals[i].name;
				for (auto &c : nm)
					if (c == ' ')
						c = '.';
				vcd_file << "$var wire " << signals[i].object->width << " "
				         << vcd_ids[i] << " " << nm << " $end\n";
			}
			vcd_file << "$upscope $end\n$enddefinitions $end\n";
		}

		std::vector<fstHandle> no_clocks;
		// -fast: only decompress inputs + regs (seed) + memory rows. Combo nets
		// are not in the mask; CXXRTL recomputes them. -reg still overwrites
		// regs each sample from the same masked handles.
		std::vector<fstHandle> fac_mask;
		if (fast) {
			for (auto *sig : seed_sigs)
				if (sig->fst_handle != 0)
					fac_mask.push_back(sig->fst_handle);
			for (auto &memory : memories)
				for (auto &row_handle : memory.fst_handles)
					if (row_handle.second != 0)
						fac_mask.push_back(row_handle.second);
			log("FST filtered replay (-fast): %d handles (inputs + regs/mems%s).\n",
			    GetSize(fac_mask), reg_overwrite ? ", -reg" : "");
		}

		auto cosim_step = [&](uint64_t time) {
			if (log_interval > 0 && sample_count > 0 && sample_count % log_interval == 0) {
				log("Completed %d samples at %lu%s\n", sample_count, (unsigned long)time, fst.getTimescaleString());
				log_flush();
			}

			// Seed all state once; later samples only drive input ports.
			if (first_sample) {
				apply_waveform(fst, seed_sigs);
				initialize_memories(fst, memories);
			} else {
				apply_waveform(fst, input_sigs);
			}
			step(handle);

			// Overwrite register values from the waveform.
			if (reg_overwrite && apply_waveform(fst, reg_sigs))
				step(handle);

			// Recalculate valid design wires whose values CXXRTL optimized away.
			refresh_outlines(outlines, eval_outline);

			// Record this sample's settled values to the debug VCD (change-based).
			if (vcd_file.is_open()) {
				vcd_file << "#" << (unsigned long long)time << "\n";
				for (size_t i = 0; i < signals.size(); i++) {
					std::string bits = value_to_bits(signals[i].object);
					if (!first_sample && bits == vcd_prev[i])
						continue;
					if (signals[i].object->width == 1)
						vcd_file << bits << vcd_ids[i] << "\n";
					else
						vcd_file << "b" << bits << " " << vcd_ids[i] << "\n";
					vcd_prev[i] = bits;
				}
			}

			// Update every wire activity/duty
			if (first_sample)
				initialize_activity(activities);
			else
				measure_activity(activities, time);

			first_sample = false;
			max_time = time;
			sample_count++;
		};

		if (fast)
			fst.reconstructAllAtTimesFiltered(no_clocks, fac_mask, startCount, stopCount, INT_MAX, cosim_step);
		else
			fst.reconstructAllAtTimes(no_clocks, startCount, stopCount, INT_MAX, cosim_step);

		// Close out high times for bits still high at the end
		for (auto &act : activities)
			for (size_t bit = 0; bit < act.width; bit++)
				if ((act.prev[bit / 32] >> (bit % 32)) & 1)
					act.high_times[bit] += max_time - act.last_change[bit];

		log("Re-simulation complete: %d samples at %lu%s\n", sample_count, (unsigned long)max_time, fst.getTimescaleString());

		// Determine the clock period.
		double clk_period;
		if (clk_period_override > 0) {
			clk_period = clk_period_override;
		} else {
			double highest_toggle = 0;
			for (auto &act : activities)
				for (size_t bit = 0; bit < act.width; bit++)
					if (act.toggle_counts[bit] > highest_toggle)
						highest_toggle = act.toggle_counts[bit];
			if (highest_toggle < 2) {
				log_warning("Clock signal not found, setting frequency to 1GHz...\n");
				clk_period = 1.0 / 1.0e9;
			} else {
				clk_period = real_timescale * (double)max_time / (highest_toggle / 2.0);
			}
		}

		// Annotate the design using the sim -activity attribute contract.
		uint64_t duration = max_time;
		double frequency = 1.0 / clk_period;
		std::stringstream ss;
		ss << std::setprecision(4) << real_timescale;
		auto set_mod_timing = [&](Module *mod) {
			mod->set_string_attribute("$FREQUENCY", std::to_string(frequency));
			mod->set_string_attribute("$DURATION", std::to_string(duration));
			mod->set_string_attribute("$TIMESCALE", ss.str());
		};
		if (cut_mode) {
			for (Module *mod : cut_modules)
				set_mod_timing(mod);
		} else {
			set_mod_timing(top);
		}

		double total_activity = 0, total_duty = 0;
		uint64_t total_bits = 0;
		double cycles_total = ((double)duration * real_timescale / clk_period) * 2.0;

		dict<Wire*, SignalActivity*> wire_activities;
		int unresolved_names = 0;
		for (auto &sig : signals) {
			if (sig.wire == nullptr) {
				unresolved_names++;
				continue;
			}
			if (!wire_activities.count(sig.wire))
				wire_activities[sig.wire] = sig.activity;
		}

		for (auto &wire_activity : wire_activities) {
			Wire *wire = wire_activity.first;
			SignalActivity &act = *wire_activity.second;
			int width = std::min(wire->width, (int)act.width);
			// Count every bit (including unused/dead output bits) so activity/duty
			// matches the sim pass ground truth, which does not special-case them.
			std::string activity_str, duty_str;
			for (int i = 0; i < width; i++) {
				double activity = cycles_total > 0 ? act.toggle_counts[i] / cycles_total : 0.0;
				double duty = duration > 0 ? (double)act.high_times[i] / (double)duration : 0.0;
				total_activity += activity;
				total_duty += duty;
				total_bits++;
				activity_str += std::to_string(activity) + " ";
				duty_str += std::to_string(duty) + " ";
			}
			wire->set_string_attribute("$ACKT", activity_str);
			wire->set_string_attribute("$DUTY", duty_str);
		}

		log("Annotated activity/duty on %d unique wires; %d CXXRTL signal names were unresolved.\n",
		    GetSize(wire_activities), unresolved_names);
		if (debug && unresolved_names > 0)
			for (auto &sig : signals)
				if (sig.wire == nullptr)
					log_debug("  unresolved CXXRTL signal: %s\n", sig.name.c_str());
		if (total_bits > 0) {
			log("Average activity : %f\n", total_activity / total_bits);
			log("Average duty     : %f\n", total_duty / total_bits);
		}
		log_flush();

		destroy_handle(handle);
		dlclose(so);
	}
} CxxrtlSimPass;

PRIVATE_NAMESPACE_END
