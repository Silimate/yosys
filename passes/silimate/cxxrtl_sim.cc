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
#include <dlfcn.h>

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

// Function pointer types for the C API symbols resolved from the evaluator.
// The C API implementation is compiled into the evaluator itself (-DCXXRTL_INCLUDE_CAPI_IMPL).
typedef cxxrtl_toplevel (*fn_design_create)();                     // build design object in C++
typedef cxxrtl_handle (*fn_create)(cxxrtl_toplevel);               // wrap design in runnable handle
typedef void (*fn_destroy)(cxxrtl_handle);                         // tear down design
typedef size_t (*fn_step)(cxxrtl_handle);                          // evaluate the circuit once (between two #timestamps)
typedef void (*fn_enum)(cxxrtl_handle, void *,                     // walk over every visible signal ($var)
	void (*)(void *, const char *, struct cxxrtl_object *, size_t));
typedef void (*fn_outline_eval)(cxxrtl_outline);                   // recompute OUTLINE signal values (optimized nets)

// Switching activity (toggles + high time) measured for one simulated net.
struct SignalActivity {
	struct cxxrtl_object *object;        // CXXRTL simulation-side descriptor of the netlist wire
	size_t num_words;                    // number of 32-bit chunks to hold the value
	std::vector<uint32_t> prev;          // previous sample value
	std::vector<double> toggle_counts;   // per-bit toggle counts
	std::vector<uint64_t> high_times;    // per-bit accumulated high time
	std::vector<uint64_t> last_change;   // per-bit time of last observed change
	cxxrtl_outline outline;              // non-null for OUTLINE items (needs eval)
};

// One named signal/port/register of the design, linked to its simulation storage and matching waveform signal.
struct DesignSignal {
	std::string name;       // full hierarchical item name (space-separated)
	Wire *wire;             // wire in the main design, or nullptr
	int tracker;            // index into trackers
	fstHandle fst_handle;   // matching FST signal, or 0
	bool is_input;          // top-level input: driven from FST every sample
	bool is_sync;           // sync-driven (register): -reg overwrite target
	bool writable;          // object->next != NULL
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
		log("        precompiled evaluator (see cxxrtl_compile).\n");
		log("\n");
		log("    -module <name>\n");
		log("        the design module the evaluator was emitted from.\n");
		log("\n");
		log("    -r <file.fst|file.vcd>\n");
		log("        input waveform; VCD is converted via vcd2fst (required).\n");
		log("\n");
		log("    -scope <name>\n");
		log("        scope within the file to query from for the given module/evaluator.\n");
		log("\n");
		log("    -clk-period <seconds>\n");
		log("        master clock period override. Otherwise, derives from the fastest-toggling signal and");
		log("        assumes it's clock period from the timescale of the waveform.\n");
		log("\n");
		log("    -start <time>, -stop <time>\n");
		log("        replay window; bare numbers are ns, unit suffixes (us/ns/ps/...)\n");
		log("        and END are accepted, like the sim pass (default: full range).\n");
		log("\n");
		log("    -reg\n");
		log("        overwrite register states from the waveform every sample.\n");
		log("\n");
		log("    -log-interval <n>\n");
		log("        log progress every <n> samples.\n");
		log("\n");
		log("    -d\n");
		log("        enable debug output.\n");
		log("\n");
	}

	// --- name mapping -----------------------------------------------------

	// Resolve a debug item name to a wire of the hierarchical design.
	// Item names are space-separated: leading components are instance names,
	// the last component is the wire name (possibly dotted after flatten).
	Wire *find_wire(Design *design, Module *top, const std::string &item_name)
	{
		std::vector<std::string> parts;
		size_t pos = 0;
		while (pos <= item_name.size()) {
			size_t sp = item_name.find(' ', pos);
			if (sp == std::string::npos) sp = item_name.size();
			parts.push_back(item_name.substr(pos, sp - pos));
			pos = sp + 1;
		}
		if (parts.empty())
			return nullptr;

		// Descend through the instance path
		Module *mod = top;
		for (size_t i = 0; i + 1 < parts.size(); i++) {
			Cell *cell = mod->cell(RTLIL::escape_id(parts[i]));
			if (cell == nullptr)
				return nullptr;
			Module *child = design->module(cell->type);
			if (child == nullptr)
				return nullptr;
			mod = child;
		}

		// Resolve the wire name, walking dotted prefixes (flattened paths)
		// down the hierarchy as needed.
		std::string name = parts.back();
		while (true) {
			Wire *w = mod->wire(RTLIL::escape_id(name));
			if (w != nullptr)
				return w;
			size_t dot = name.find('.');
			if (dot == std::string::npos)
				return nullptr;
			Cell *cell = mod->cell(RTLIL::escape_id(name.substr(0, dot)));
			if (cell == nullptr)
				return nullptr;
			Module *child = design->module(cell->type);
			if (child == nullptr)
				return nullptr;
			mod = child;
			name = name.substr(dot + 1);
		}
	}

	// --- pass entry point ---------------------------------------------------

	void execute(std::vector<std::string> args, Design *design) override
	{
		log_header(design, "Executing CXXRTL_SIM pass (FST-driven CXXRTL re-simulation).\n");

		std::string so_path, wave_path, scope, module_name;
		double clk_period_override = 0;
		double start_time = 0, stop_time = -1;
		int log_interval = 0;
		bool reg_overwrite = false;
		bool debug = false;

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
			if (args[argidx] == "-reg") {
				reg_overwrite = true;
				continue;
			}
			if (args[argidx] == "-d") {
				debug = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (so_path.empty())
			log_cmd_error("-so <file.so> is required.\n");
		if (wave_path.empty())
			log_cmd_error("-r <waveform> is required.\n");

		// The annotation root: an explicit module, or the design top
		bool module_mode = !module_name.empty();
		Module *top;
		if (module_mode) {
			top = design->module(RTLIL::escape_id(module_name));
			if (top == nullptr)
				log_cmd_error("Module '%s' not found in design.\n", module_name.c_str());
		} else {
			top = design->top_module();
			if (top == nullptr)
				log_cmd_error("No top module found; run `hierarchy -top <module>` first.\n");
		}

		// 1. Load the precompiled evaluator
		void *so = dlopen(so_path.c_str(), RTLD_NOW | RTLD_LOCAL);
		if (so == nullptr)
			log_cmd_error("dlopen(%s) failed: %s\n", so_path.c_str(), dlerror());

		auto design_create = (fn_design_create)dlsym(so, "cxxrtl_design_create");
		auto capi_create = (fn_create)dlsym(so, "cxxrtl_create");
		auto capi_destroy = (fn_destroy)dlsym(so, "cxxrtl_destroy");
		auto capi_step = (fn_step)dlsym(so, "cxxrtl_step");
		auto capi_enum = (fn_enum)dlsym(so, "cxxrtl_enum");
		auto capi_outline_eval = (fn_outline_eval)dlsym(so, "cxxrtl_outline_eval");
		if (!design_create || !capi_create || !capi_destroy || !capi_step || !capi_enum ||
		    !capi_outline_eval)
			log_cmd_error("Missing CXXRTL C API symbols in %s.\n", so_path.c_str());

		cxxrtl_handle handle = capi_create(design_create());

		// 2. Enumerate debug items, dedupe storage, set up trackers
		std::vector<DesignSignal> items;
		std::vector<SignalActivity> trackers;
		dict<uintptr_t, int> storage_to_tracker;

		struct EnumCtx {
			CxxrtlSimPass *self;
			std::vector<DesignSignal> *items;
			std::vector<SignalActivity> *trackers;
			dict<uintptr_t, int> *storage_to_tracker;
			Design *design;
			Module *top;
		} ctx = { this, &items, &trackers, &storage_to_tracker, design, top };

		capi_enum(handle, &ctx, [](void *data, const char *name, struct cxxrtl_object *object, size_t parts) {
			EnumCtx *ctx = (EnumCtx*)data;
			if (parts != 1)
				return; // multi-part objects unsupported (post-splitnets)
			if (object->type == CXXRTL_MEMORY)
				return; // memories are not annotated
			if (object->depth != 1 || object->width == 0)
				return;
			// OUTLINE items are inlined/optimized combinational nets whose
			// value is only valid right after cxxrtl_outline_eval(); we still
			// track them so internal wires get activity, not just ports/regs.

			DesignSignal info;
			info.name = name;
			info.wire = ctx->self->find_wire(ctx->design, ctx->top, info.name);
			info.is_input = (object->flags & CXXRTL_INPUT) != 0;
			info.is_sync = (object->flags & CXXRTL_DRIVEN_SYNC) != 0;
			info.writable = object->next != nullptr;
			info.fst_handle = 0;

			uintptr_t key = (uintptr_t)object->curr;
			auto it = ctx->storage_to_tracker->find(key);
			if (it == ctx->storage_to_tracker->end()) {
				SignalActivity t;
				t.object = object;
				t.num_words = (object->width + 31) / 32;
				t.prev.assign(t.num_words, 0);
				t.toggle_counts.assign(object->width, 0.0);
				t.high_times.assign(object->width, 0);
				t.last_change.assign(object->width, 0);
				t.outline = (object->type == CXXRTL_OUTLINE) ? object->outline : nullptr;
				int idx = GetSize(*ctx->trackers);
				ctx->trackers->push_back(std::move(t));
				ctx->storage_to_tracker->emplace(key, idx);
				info.tracker = idx;
			} else {
				info.tracker = it->second;
			}
			ctx->items->push_back(std::move(info));
		});

		log_debug("Enumerated %d debug items (%d unique storages).\n", GetSize(items), GetSize(trackers));

		// 3. Open the waveform and match signals
		FstData fst(wave_path);
		double real_timescale = pow(10.0, fst.getScale());

		if (scope.empty()) {
			scope = fst.autoScope(top);
			if (scope.empty())
				log_cmd_error("No scope found for module '%s'. Please specify -scope.\n",
				              RTLIL::unescape_id(top->name).c_str());
		}
		log("Using scope: \"%s\"\n", scope.c_str());

		int found_inputs = 0, n_inputs = 0;
		int found_regs = 0, n_regs = 0;
		for (auto &info : items) {
			// FST names use '.' both for hierarchy and flattened wire names
			std::string fst_name = scope + "." + info.name;
			for (auto &c : fst_name)
				if (c == ' ') c = '.';
			info.fst_handle = fst.getHandle(fst_name);

			// Verify every signal we will drive from the waveform can be
			// found before the replay loop drives it; warn otherwise.
			if (info.is_input) {
				n_inputs++;
				if (info.fst_handle != 0)
					found_inputs++;
				else
					log_warning("Input port '%s' not found in waveform; left at its initial value.\n",
					            fst_name.c_str());
			} else if (reg_overwrite && info.is_sync && info.writable) {
				n_regs++;
				if (info.fst_handle != 0)
					found_regs++;
				else if (debug)
					log_warning("Register '%s' not found in waveform; not overwritten.\n",
					            fst_name.c_str());
			}
		}
		log("Driving %d/%d input ports from the waveform.\n", found_inputs, n_inputs);
		if (reg_overwrite)
			log("Overwriting %d/%d registers from the waveform.\n", found_regs, n_regs);
		if (n_inputs > 0 && found_inputs == 0) {
			// Without any driven input the replay would be meaningless. In
			// module mode skip this module (workers handle many); for a
			// whole-design run it is a hard configuration error.
			if (module_mode) {
				log_warning("No input ports of module '%s' matched in the waveform "
				            "(scope \"%s\"); skipping annotation.\n",
				            module_name.c_str(), scope.c_str());
				capi_destroy(handle);
				dlclose(so);
				return;
			}
			log_cmd_error("No input ports matched in the waveform; check -scope.\n");
		}

		// 4. Replay (start/stop semantics mirror the sim pass)
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

		// Write an FST value string (MSB first; x/z mapped to 0) into an object
		auto write_object = [](struct cxxrtl_object *object, const std::string &v) -> bool {
			size_t num_words = (object->width + 31) / 32;
			bool changed = false;
			uint32_t *tgt = object->next != nullptr ? object->next : object->curr;
			std::vector<uint32_t> val(num_words, 0);
			size_t nbits = std::min((size_t)v.size(), object->width);
			for (size_t i = 0; i < nbits; i++) {
				char c = v[v.size() - 1 - i]; // FST strings are MSB first
				if (c == '1')
					val[i / 32] |= (uint32_t)1 << (i % 32);
			}
			for (size_t w = 0; w < num_words; w++) {
				if (tgt[w] != val[w])
					changed = true;
				tgt[w] = val[w];
			}
			// For wires (separate curr/next), also force curr so the value
			// is visible without an extra commit (used for init/reg overwrite).
			if (object->next != nullptr && object->next != object->curr)
				for (size_t w = 0; w < num_words; w++)
					object->curr[w] = val[w];
			return changed;
		};

		// Outlines must be re-evaluated each sample to read a valid value.
		bool have_outlines = false;
		for (auto &t : trackers)
			if (t.outline != nullptr) { have_outlines = true; break; }

		bool initial = true;
		uint64_t max_time = startCount;
		int cycle = 0;

		std::vector<fstHandle> no_clocks;
		fst.reconstructAllAtTimes(no_clocks, startCount, stopCount, INT_MAX, [&](uint64_t time) {
			if (log_interval > 0 && cycle > 0 && cycle % log_interval == 0) {
				log("Completed %d samples at %lu%s\n", cycle, (unsigned long)time, fst.getTimescaleString());
				log_flush();
			}

			if (initial) {
				// Initialize every matched, writable signal from the waveform
				for (auto &info : items) {
					if (info.fst_handle == 0 || !info.writable)
						continue;
					write_object(trackers[info.tracker].object, fst.valueOf(info.fst_handle));
				}
			} else {
				// Drive top-level inputs
				for (auto &info : items) {
					if (!info.is_input || info.fst_handle == 0)
						continue;
					write_object(trackers[info.tracker].object, fst.valueOf(info.fst_handle));
				}
			}

			capi_step(handle);

			// Overwrite register ground truth from the waveform
			if (reg_overwrite && !initial) {
				bool diverged = false;
				for (auto &info : items) {
					if (!info.is_sync || !info.writable || info.fst_handle == 0)
						continue;
					diverged |= write_object(trackers[info.tracker].object, fst.valueOf(info.fst_handle));
				}
				if (diverged)
					capi_step(handle);
			}

			// Refresh outline (inlined) nets: their curr buffer is only
			// meaningful right after an eval and goes stale after each step.
			if (have_outlines)
				for (auto &t : trackers)
					if (t.outline != nullptr)
						capi_outline_eval(t.outline);

			if (initial) {
				// First sample: snapshot state, don't count
				for (auto &t : trackers) {
					for (size_t w = 0; w < t.num_words; w++)
						t.prev[w] = t.object->curr[w];
					for (size_t bit = 0; bit < t.object->width; bit++)
						t.last_change[bit] = time;
				}
				initial = false;
			} else {
				// Count toggles / accumulate high times (lazy, per changed word)
				for (auto &t : trackers) {
					const uint32_t *curr = t.object->curr;
					for (size_t w = 0; w < t.num_words; w++) {
						uint32_t diff = curr[w] ^ t.prev[w];
						while (diff != 0) {
							int b = __builtin_ctz(diff);
							diff &= diff - 1;
							size_t bit = w * 32 + b;
							if (bit >= t.object->width)
								break;
							if ((t.prev[w] >> b) & 1)
								t.high_times[bit] += time - t.last_change[bit];
							t.last_change[bit] = time;
							t.toggle_counts[bit] += 1.0;
						}
						t.prev[w] = curr[w];
					}
				}
			}

			max_time = time;
			cycle++;
		});

		// Close out high times for bits still high at the end
		for (auto &t : trackers)
			for (size_t bit = 0; bit < t.object->width; bit++)
				if ((t.prev[bit / 32] >> (bit % 32)) & 1)
					t.high_times[bit] += max_time - t.last_change[bit];

		log("Re-simulation complete: %d samples at %lu%s\n", cycle, (unsigned long)max_time, fst.getTimescaleString());

		// 5. Determine the clock period
		double clk_period;
		if (clk_period_override > 0) {
			clk_period = clk_period_override;
		} else {
			double highest_toggle = 0;
			for (auto &t : trackers)
				for (size_t bit = 0; bit < t.object->width; bit++)
					if (t.toggle_counts[bit] > highest_toggle)
						highest_toggle = t.toggle_counts[bit];
			if (highest_toggle < 2) {
				log_warning("Clock signal not found, setting frequency to 1GHz...\n");
				clk_period = 1.0 / 1.0e9;
			} else {
				clk_period = real_timescale * (double)max_time / (highest_toggle / 2.0);
			}
		}

		// 6. Annotate the design (same contract as sim -activity)
		uint64_t duration = max_time;
		double frequency = 1.0 / clk_period;
		std::stringstream ss;
		ss << std::setprecision(4) << real_timescale;
		top->set_string_attribute("$FREQUENCY", std::to_string(frequency));
		top->set_string_attribute("$DURATION", std::to_string(duration));
		top->set_string_attribute("$TIMESCALE", ss.str());

		double total_activity = 0, total_duty = 0;
		uint64_t total_bits = 0;
		double cycles_total = ((double)duration * real_timescale / clk_period) * 2.0;

		for (auto &info : items) {
			if (info.wire == nullptr)
				continue;
			SignalActivity &t = trackers[info.tracker];
			int width = std::min(info.wire->width, (int)t.object->width);
			std::string activity_str, duty_str;
			for (int i = 0; i < width; i++) {
				double activity = cycles_total > 0 ? t.toggle_counts[i] / cycles_total : 0.0;
				double duty = duration > 0 ? (double)t.high_times[i] / (double)duration : 0.0;
				total_activity += activity;
				total_duty += duty;
				total_bits++;
				activity_str += std::to_string(activity) + " ";
				duty_str += std::to_string(duty) + " ";
			}
			info.wire->set_string_attribute("$ACKT", activity_str);
			info.wire->set_string_attribute("$DUTY", duty_str);
		}

		// Report coverage over the design module's own public wires: the
		// deliverable is activity/duty on every wire, which feeds activity_prop.
		int design_wires = 0, with_activity = 0;
		for (auto w : top->wires()) {
			if (!w->name.isPublic())
				continue;
			design_wires++;
			if (w->attributes.count(RTLIL::IdString("$ACKT")))
				with_activity++;
		}
		log("Annotated activity/duty on %d/%d wires of module '%s'.\n",
		    with_activity, design_wires, RTLIL::unescape_id(top->name).c_str());
		if (with_activity < design_wires) {
			log_warning("%d wire(s) of '%s' have no activity data.\n",
			            design_wires - with_activity, RTLIL::unescape_id(top->name).c_str());
			if (debug)
				for (auto w : top->wires())
					if (w->name.isPublic() && !w->attributes.count(RTLIL::IdString("$ACKT")))
						log_debug("  no activity data: wire %s (width %d)\n",
						          log_id(w->name), w->width);
		}
		if (total_bits > 0) {
			log("Average activity: %f\n", total_activity / total_bits);
			log("Average duty    : %f\n", total_duty / total_bits);
		}
		log_flush();

		capi_destroy(handle);
		dlclose(so);
	}
} CxxrtlSimPass;

PRIVATE_NAMESPACE_END
