#include "kernel/yosys_config.h"
#ifdef YOSYS_ENABLE_TCL

#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"
#include <tcl.h>
#include <list>
#include <optional>
#include <iostream>
#include <sstream>

#if TCL_MAJOR_VERSION < 9
typedef int YS_Tcl_Size;
#else
typedef Tcl_Size YS_Tcl_Size;
#endif

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct TclCall {
	Tcl_Interp *interp;
	int objc;
	Tcl_Obj* const* objv;
};

static int redirect_unknown(TclCall call);
static size_t get_node_count(Tcl_Interp* interp);

struct BitSelection {
	bool all = false;
	std::vector<bool> bits = {};
	void set_all() {
		bits.clear();
		all = true;
	}
	void clear() {
		bits.clear();
		all = false;
	}
	void set(size_t idx) {
		if (all)
			return;
		if (idx >= bits.size())
			bits.resize(idx + 1);
		bits[idx] = true;
	}
	void merge(const BitSelection& other) {
		if (all)
			return;
		if (other.all) {
			set_all();
			return;
		}
		if (other.bits.size() > bits.size())
			bits.resize(other.bits.size());
		for (size_t other_idx = 0; other_idx < other.bits.size(); other_idx++) {
			bool other_bit = other.bits[other_idx];
			if (other_bit)
				set(other_idx);
		}
	}
	void dump() {
		if (!all) {
			for (size_t i = 0; i < bits.size(); i++)
				if (bits[i])
					log("\t\t [%zu]\n", i);
		} else {
			log("\t\t FULL\n");
		}
	}
	bool is_set(size_t idx) const {
		if (all)
			return true;
		if (idx >= bits.size())
			return false;
		return bits[idx];
	}
	// TODO actually use this
	void compress(size_t size) {
		if (bits.size() < size)
			return;
		for (size_t i = 0; i < size; i++)
			if (!bits[i])
				return;
		bits.clear();
		bits.shrink_to_fit();
		all = true;
	}
};

struct SdcObjects {
	enum CollectMode {
		// getter-side object tracking with minimal features
		SimpleGetter,
		// getter-side object tracking with everything
		FullGetter,
		// constraint-side tracking
		FullConstraint,
	} collect_mode;
	using CellPin = std::pair<Cell*, IdString>;
	Design* design;
	std::vector<std::pair<std::string, Wire*>> design_ports;
	std::vector<std::pair<std::string, Cell*>> design_cells;
	std::vector<std::pair<std::string, CellPin>> design_pins;
	std::vector<std::pair<std::string, Wire*>> design_nets;

	using PortPattern = std::tuple<std::string, Wire*, BitSelection>;
	using PinPattern = std::tuple<std::string, SdcObjects::CellPin, BitSelection>;
	std::vector<std::vector<PortPattern>> resolved_port_pattern_sets;
	std::vector<std::vector<PinPattern>> resolved_pin_pattern_sets;
	// TODO

	dict<std::pair<std::string, Wire*>, BitSelection> constrained_ports;
	pool<std::pair<std::string, Cell*>> constrained_cells;
	dict<std::pair<std::string, CellPin>, BitSelection> constrained_pins;
	dict<std::pair<std::string, Wire*>, BitSelection> constrained_nets;

	// SILIMATE: what each get_ports call node resolved to, and the constants
	// set_logic_zero/set_logic_one put on those ports (sdc -constants)
	dict<size_t, std::vector<PortPattern>> port_nodes;
	std::vector<std::tuple<Wire*, BitSelection, State>> logic_constants;

	void sniff_module(std::list<std::string>& hierarchy, Module* mod) {
		std::string prefix;
		for (auto mod_name : hierarchy) {
			if (prefix.length())
				prefix += "/"; // TODO seperator?
			prefix += mod_name;
		}

		for (auto* wire : mod->wires()) {
			std::string name = wire->name.str();
			log_assert(name.length());
			// TODO: really skip internal wires?
			if (name[0] == '$')
				continue;
			name = name.substr(1);
			std::string path = prefix;
			if (path.length())
				path += "/";
			path += name;
			design_nets.push_back(std::make_pair(path, wire));
		}

		for (auto* cell : mod->cells()) {
			std::string name = cell->name.str();
			// TODO: really skip internal cells?
			if (name[0] == '$')
				continue;
			name = name.substr(1);
			std::string path = prefix;
			if (path.length())
				path += "/";
			path += name;
			design_cells.push_back(std::make_pair(path, cell));
			for (auto& pin : cell->connections()) {
				IdString pin_name = pin.first;
				std::string pin_name_sdc = path + "/" + pin.first.str().substr(1);
				design_pins.push_back(std::make_pair(pin_name_sdc, std::make_pair(cell, pin_name)));
			}
			if (auto sub_mod = mod->design->module(cell->type)) {
				hierarchy.push_back(name);
				sniff_module(hierarchy, sub_mod);
				hierarchy.pop_back();
			}
		}
	}
	SdcObjects(Design* design) : design(design) {
		Module* top = design->top_module();
		if (!top)
			log_error("Top module couldn't be determined. Check 'top' attribute usage");
		for (auto port : top->ports) {
			RTLIL::Wire *wire = top->wire(port);
			if (!wire) {
				// This should not be possible. See https://github.com/YosysHQ/yosys/pull/5594#issue-3791198573
				log_error("Port %s doesn't exist", port.unescape());
			}
			design_ports.push_back(std::make_pair(port.str().substr(1), wire));
		}
		std::list<std::string> hierarchy{};
		sniff_module(hierarchy, top);
	}
	~SdcObjects() = default;

	template <typename T, typename U>
	void build_normal_result(Tcl_Interp* interp, std::vector<std::tuple<std::string, T, BitSelection>>&& resolved, U& tgt, std::function<size_t(T&)> width, Tcl_Obj*& result) {
		if (!result)
			result = Tcl_NewListObj(resolved.size(), nullptr);
		for (auto [name, obj, matching_bits] : resolved) {
			for (size_t i = 0; i < width(obj); i++)
				if (matching_bits.is_set(i)) {
					Tcl_ListObjAppendElement(interp, result, Tcl_NewStringObj(name.c_str(), name.size()));
					break;
				}

		}
		size_t node_count = get_node_count(interp);
		tgt.emplace_back(std::move(resolved));
		log("%zu %zu\n", node_count, tgt.size());
		log_assert(node_count == tgt.size());
	}
	template <typename T>
	void merge_as_constrained(std::vector<std::tuple<std::string, T, BitSelection>>&& resolved) {
		for (auto [name, obj, matching_bits] : resolved) {
			merge_or_init(std::make_pair(name, obj), constrained_pins, matching_bits);
		}
	}
	void dump() {
		std::sort(design_ports.begin(), design_ports.end());
		std::sort(design_cells.begin(), design_cells.end());
		std::sort(design_pins.begin(), design_pins.end());
		std::sort(design_nets.begin(), design_nets.end());
		constrained_ports.sort();
		constrained_cells.sort();
		constrained_pins.sort();
		constrained_nets.sort();
		// log("Design ports:\n");
		// for (auto name : design_ports) {
		// 	log("\t%s\n", name.c_str());
		// }
		// log("Design cells:\n");
		// for (auto [name, cell] : design_cells) {
		// 	(void)cell;
		// 	log("\t%s\n", name.c_str());
		// }
		// log("Design pins:\n");
		// for (auto [name, pin] : design_pins) {
		// 	(void)pin;
		// 	log("\t%s\n", name.c_str());
		// }
		// log("Design nets:\n");
		// for (auto [name, net] : design_nets) {
		// 	(void)net;
		// 	log("\t%s\n", name.c_str());
		// }
		// log("\n");
		log("Constrained ports:\n");
		for (auto [ref, bits] : constrained_ports) {
			auto [name, port] = ref;
			(void)port;
			log("\t%s\n", name.c_str());
			bits.dump();
		}
		log("Constrained cells:\n");
		for (auto& [name, cell] : constrained_cells) {
			(void)cell;
			log("\t%s\n", name.c_str());
		}
		log("Constrained pins:\n");
		for (auto& [ref, bits] : constrained_pins) {
			auto [name, pin] = ref;
			(void)pin;
			log("\t%s\n", name.c_str());
			bits.dump();
		}
		log("Constrained nets:\n");
		for (auto& [ref, bits] : constrained_nets) {
			auto [name, net] = ref;
			(void)net;
			log("\t%s\n", name.c_str());
			bits.dump();
		}
		log("\n");
	}

	class KeepHierarchyWorker {
		std::unordered_set<Module*> tracked_modules = {};
		Design* design = nullptr;
		bool mark(Module* mod) {
			for (auto* cell : mod->cells()) {
				if (auto* submod = design->module(cell->type))
					if (mark(submod)) {
						mod->set_bool_attribute(ID::keep_hierarchy);
						return true;
					}
			}

			if (tracked_modules.count(mod)) {
				mod->set_bool_attribute(ID::keep_hierarchy);
				return true;
			}

			return false;
		}
	public:
		KeepHierarchyWorker(SdcObjects* objects, Design* d) : design(d) {
			for (auto [ref, _] : objects->constrained_ports) {
				tracked_modules.insert(ref.second->module);
			}
			for (auto& [_, cell] : objects->constrained_cells) {
				tracked_modules.insert(cell->module);
			}
			for (auto& [ref, _] : objects->constrained_pins) {
				tracked_modules.insert(ref.second.first->module);
			}
			for (auto& [ref, _] : objects->constrained_nets) {
				tracked_modules.insert(ref.second->module);
			}
			log_debug("keep_hierarchy tracked modules:\n");
			for (auto* mod : tracked_modules)
				log_debug("\t%s\n", mod->name);
		}
		bool mark() {
			return mark(design->top_module());
		}
	};
	void keep_hierarchy() {
		(void)KeepHierarchyWorker(this, design).mark();
	}
	// SILIMATE: drive every reader of a top input port bit set_logic_zero/set_logic_one
	// named from its constant instead. The port itself stays, so the SDC still finds it.
	void tie_logic_constants() {
		Module* top = design->top_module();
		dict<SigBit, State> tied;
		for (auto& [wire, bits, value] : logic_constants) {
			if (!wire->port_input || wire->port_output) {
				log_warning("set_logic on %s skipped: only input ports can be tied.\n", log_id(wire));
				continue;
			}
			// The SDC numbers bits as the HDL declares them ([7:4], [0:3]), not by RTLIL offset
			std::vector<int> offsets;
			if (bits.all)
				for (int i = 0; i < wire->width; i++)
					offsets.push_back(i);
			for (size_t idx = 0; !bits.all && idx < bits.bits.size(); idx++)
				if (bits.bits[idx]) {
					int offset = wire->from_hdl_index(idx);
					if (offset == INT_MIN)
						log_warning("set_logic on %s[%zu] skipped: no such bit.\n", log_id(wire), idx);
					else
						offsets.push_back(offset);
				}
			for (int offset : offsets)
				tied[SigBit(wire, offset)] = value; // a later command wins, as in STA
		}
		if (tied.empty())
			return;
		if (!top->processes.empty())
			log_warning("Module %s has processes, which keep reading the tied ports; run proc first.\n", log_id(top));
		auto tie = [&](const SigSpec& sig) {
			SigSpec out;
			for (auto bit : sig)
				out.append(tied.count(bit) ? SigBit(tied.at(bit)) : bit);
			return out;
		};
		for (auto cell : top->cells())
			for (auto& [port, sig] : dict<IdString, SigSpec>(cell->connections())) {
				SigSpec tied_sig = tie(sig);
				if (cell->input(port) && tied_sig != sig)
					cell->setPort(port, tied_sig);
			}
		std::vector<SigSig> conns;
		for (auto& [lhs, rhs] : top->connections())
			conns.push_back({lhs, tie(rhs)});
		top->new_connections(conns);
		log("Tied %d input port bit(s) to the constants set_logic_zero/set_logic_one gave them.\n", GetSize(tied));
	}
};

// TODO vectors
// TODO cell arrays?
struct MatchConfig {
	enum MatchMode {
		WILDCARD,
		REGEX,
	} match;
	bool match_case;
	enum HierMode {
		FLAT,
		TREE,
	} hier;
	MatchConfig(bool regexp_flag, bool nocase_flag, bool hierarchical_flag) :
		match(regexp_flag ? REGEX : WILDCARD),
		match_case(!nocase_flag),
		hier(hierarchical_flag ? FLAT : TREE) { }
};

static std::pair<bool, BitSelection> matches(std::string name, const std::string& pat, const MatchConfig& config) {
	(void)config;
	bool got_bit_index = false;;
	int bit_idx;
	std::string pat_base = pat;
	size_t pos = pat.rfind('[');
	if (pos != std::string::npos) {
		got_bit_index = true;
		pat_base = pat.substr(0, pos);
		std::string bit_selector = pat.substr(pos + 1, pat.rfind(']') - pos - 1);
		for (auto c : bit_selector)
			if (!std::isdigit(c))
				log_error("Unsupported bit selector %s in SDC pattern %s\n",
							bit_selector.c_str(), pat.c_str());
		bit_idx = std::stoi(bit_selector);

	}
	BitSelection bits = {};
	if (name == pat_base) {
		if (got_bit_index) {
			bits.set(bit_idx);
			return std::make_pair(true, bits);
		} else {
			bits.set_all();
			return std::make_pair(true, bits);

		}
	} else {
		return std::make_pair(false, bits);
	}
}

static int getter_graph_node(TclCall call) {
	// Insert -getter-validated as first argument for passing to unknown
	// to distinguish resolved and unknown getters.
	// For example, if call is ["get_foo", "-bar"]
	// then newCall is ["get_foo", "-getter-validated", "-bar"]
	Tcl_Obj* validity_tag = Tcl_NewStringObj("-getter-validated", -1);
	Tcl_IncrRefCount(validity_tag);
	std::vector<Tcl_Obj*> newObjv(call.objc + 1);
	log_assert(call.objc > 0);
	newObjv[0] = call.objv[0];
	newObjv[1] = validity_tag;
	for (int i = 1; i < call.objc; ++i) {
		newObjv[i + 1] = call.objv[i];
	}
	// Send the vector to the Tcl land
	Tcl_Obj** allocatedObjv = (Tcl_Obj**)Tcl_Alloc((call.objc + 1) * sizeof(Tcl_Obj*));
	for (int i = 0; i < call.objc + 1; ++i) {
		allocatedObjv[i] = newObjv[i];
	}
	TclCall newCall {
		.interp = call.interp,
		.objc = call.objc + 1,
		.objv = allocatedObjv
	};
	// Finally, redirect to unknown handler
	return redirect_unknown(newCall);
}

static int redirect_unknown(TclCall call) {
	// TODO redirect to different command
	Tcl_Obj *newCmd = Tcl_NewStringObj("unknown", -1);
	auto newObjc = call.objc + 1;
	Tcl_Obj** newObjv = (Tcl_Obj**)Tcl_Alloc(newObjc * sizeof(Tcl_Obj*));
	newObjv[0] = newCmd;
	for (int i = 1; i < newObjc; i++) {
		newObjv[i] = call.objv[i - 1];
	}
	int result = Tcl_EvalObjv(call.interp, newObjc, newObjv, 0);
	Tcl_DecrRefCount(newCmd);
	Tcl_Free((char*) newObjv);
	return result;
}


struct SdcGraphNode {
	using Child = std::variant<SdcGraphNode*, std::string>;
	std::vector<Child> children;
	SdcGraphNode() = default;
	void addChild(SdcGraphNode* child) {
		children.push_back(child);
	}
	void addChild(std::string tcl_string) {
		children.push_back(tcl_string);
	}
	void dump(std::ostream& os) const {
		bool first = true;
		for (auto child : children) {
			if (first) {
				first = false;
			} else {
				os << " ";
			}
			if (auto* s = std::get_if<std::string>(&child))
				os << *s;
			else if (SdcGraphNode*& c = *std::get_if<SdcGraphNode*>(&child)) {
				os << "[";
				c->dump(os);
				os << "]";
			} else {
				log_assert(false);
			}
		}
	}
};

// SILIMATE: the graph node index a YOSYS_SDC_MAGIC_NODE_<n> string names, if it is one
static std::optional<size_t> magic_node_index(const std::string& arg) {
	const std::string prefix = "YOSYS_SDC_MAGIC_NODE_";
	if (arg.compare(0, prefix.size(), prefix) != 0 || arg.size() == prefix.size())
		return std::nullopt;
	for (size_t i = prefix.size(); i < arg.size(); i++)
		if (!std::isdigit(arg[i]))
			return std::nullopt;
	return std::stoul(arg.substr(prefix.size()));
}

static size_t get_node_count(Tcl_Interp* interp) {
	const char* idx_raw = Tcl_GetVar(interp, "sdc_call_index", TCL_GLOBAL_ONLY);
	log_assert(idx_raw);
	std::string idx(idx_raw);
	for (auto c : idx)
		if (!std::isdigit(c))
			log_error("sdc_call_index non-numeric value %s\n", idx.c_str());
	return std::stoi(idx);
}

std::vector<std::vector<std::string>> gather_nested_calls(Tcl_Interp* interp) {

	Tcl_Obj* listObj = Tcl_GetVar2Ex(interp, "sdc_calls", nullptr, TCL_GLOBAL_ONLY);
	YS_Tcl_Size listLength;

	std::vector<std::vector<std::string>> sdc_calls;
	if (Tcl_ListObjLength(interp, listObj, &listLength) == TCL_OK) {
		for (int i = 0; i < listLength; i++) {
			Tcl_Obj* subListObj;
			std::vector<std::string> subList;
			if (Tcl_ListObjIndex(interp, listObj, i, &subListObj) != TCL_OK) {
				log_error("broken list of lists\n");
			}
			YS_Tcl_Size subListLength;
			if (Tcl_ListObjLength(interp, subListObj, &subListLength) == TCL_OK) {
				// Valid list - extract elements
				for (int j = 0; j < subListLength; j++) {
					Tcl_Obj* elementObj;
					if (Tcl_ListObjIndex(interp, subListObj, j, &elementObj) == TCL_OK) {
						const char* elementStr = Tcl_GetString(elementObj);
						subList.push_back(std::string(elementStr));
					}
				}
			} else {
				// Single element, not a list
				const char* elementStr = Tcl_GetString(subListObj);
				subList.push_back(std::string(elementStr));
			}
			sdc_calls.push_back(subList);
		}
	}
	log_assert(sdc_calls.size() == get_node_count(interp));
	return sdc_calls;
}

std::vector<SdcGraphNode> build_graph(const std::vector<std::vector<std::string>>& sdc_calls) {
	size_t node_count = sdc_calls.size();
	std::vector<SdcGraphNode> graph(node_count);
	for (size_t i = 0; i < node_count; i++) {
		auto& new_node = graph[i];
		for (size_t j = 0; j < sdc_calls[i].size(); j++) {
			auto arg = sdc_calls[i][j];
			// SILIMATE: a list argument can hold several nodes ("[get_clocks a] [get_clocks b]");
			// anything else that is not all nodes stays a plain string
			std::istringstream tokens(arg);
			std::vector<size_t> nodes;
			std::string token;
			bool all_nodes = true;
			while (all_nodes && tokens >> token) {
				auto idx = magic_node_index(token);
				all_nodes = idx && *idx < graph.size();
				if (all_nodes)
					nodes.push_back(*idx);
			}
			if (all_nodes && !nodes.empty())
				for (auto idx : nodes)
					new_node.addChild(&graph[idx]);
			else
				new_node.addChild(arg);

		}
	}
	return graph;
}

std::vector<bool> node_ownership(const std::vector<SdcGraphNode>& graph) {
	std::vector<bool> has_parent(graph.size());
	for (auto node : graph) {
		for (auto child : node.children) {
			if (SdcGraphNode** pp = std::get_if<SdcGraphNode*>(&child)) {
				size_t idx = std::distance(&graph.front(), (const SdcGraphNode*)*pp);
				log_assert(idx < has_parent.size());
				has_parent[idx] = true;
			}
		}
	}
	return has_parent;
}

void dump_sdc_graph(const std::vector<SdcGraphNode>& graph, const std::vector<bool>& has_parent) {
	for (size_t i = 0; i < graph.size(); i++) {
		if (!has_parent[i]) {
			graph[i].dump(std::cout);
			std::cout << "\n";
		}
	}
}

void inspect_globals(Tcl_Interp* interp, bool dump_mode) {
	std::vector<std::vector<std::string>> sdc_calls = gather_nested_calls(interp);
	std::vector<SdcGraphNode> graph = build_graph(sdc_calls);
	if (dump_mode)
		dump_sdc_graph(graph, node_ownership(graph));
}

// patterns -> (pattern-object-bit)s
template <typename T, typename U>
std::vector<std::tuple<std::string, T, BitSelection>>
find_matching(U objects, const MatchConfig& config, const std::vector<std::string> &patterns, const char* obj_type)
{
	std::vector<std::tuple<std::string, T, BitSelection>> resolved;
	for (auto pat : patterns) {
		bool found = false;
		for (auto [name, obj] : objects) {
			auto [does_match, matching_bits] = matches(name, pat, config);
			if (does_match) {
				found = true;
				resolved.push_back(std::make_tuple(name, obj, matching_bits));
				// TODO add a continue statement, conditional on config
			}
		}
		if (!found)
			log_warning("No matches in design for %s %s\n", obj_type, pat.c_str());
	}
	return resolved;
}

struct TclOpts {
	const char* name;
	std::initializer_list<const char*> legals;
	TclOpts(const char* name, std::initializer_list<const char*> legals) : name(name), legals(legals)  {}
	bool parse_opt(Tcl_Obj* obj, const char* opt_name) {
		char* arg = Tcl_GetString(obj);
		std::string expected = std::string("-") + opt_name;
		if (expected == arg) {
			if (!std::find_if(legals.begin(), legals.end(),
					[&opt_name](const char* str) { return opt_name == str; }))
				log_cmd_error("Illegal argument %s for %s.\n", expected.c_str(), name);
			return true;
		}
		return false;
	}
};

struct GetterOpts : TclOpts {
	bool hierarchical_flag = false;
	bool regexp_flag = false;
	bool nocase_flag = false;
	std::string separator = "/";
	Tcl_Obj* of_objects = nullptr;
	std::vector<std::string> patterns = {};
	GetterOpts(const char* name, std::initializer_list<const char*> legals) : TclOpts(name, legals) {}
	template<typename T>
	bool parse_flag(Tcl_Obj* obj, const char* flag_name, T& flag_var) {
		bool ret = parse_opt(obj, flag_name);
		if (ret)
			flag_var = true;
		return ret;
	}
	void parse(int objc, Tcl_Obj* const objv[]) {
		int i = 1;
		for (; i < objc; i++) {
			if (parse_flag(objv[i], "hierarchical", hierarchical_flag)) continue;
			if (parse_flag(objv[i], "hier", hierarchical_flag)) continue;
			if (parse_flag(objv[i], "regexp", regexp_flag)) continue;
			if (parse_flag(objv[i], "nocase", nocase_flag)) continue;
			if (parse_opt(objv[i], "hsc")) {
				log_assert(i + 1 < objc);
				separator = Tcl_GetString(objv[++i]);
				continue;
			}
			if (parse_opt(objv[i], "of_objects")) {
				log_assert(i + 1 < objc);
				of_objects = objv[++i];
				continue;
			}
			break;
		}
		// SILIMATE: each argument is a Tcl list of patterns, as in STA tools: get_ports {a b}
		// names two ports, and get_ports { a } names a, not " a "
		for (; i < objc; i++) {
			YS_Tcl_Size count = 0;
			Tcl_Obj** elems = nullptr;
			if (Tcl_ListObjGetElements(nullptr, objv[i], &count, &elems) != TCL_OK) {
				patterns.push_back(Tcl_GetString(objv[i]));
				continue;
			}
			for (YS_Tcl_Size j = 0; j < count; j++)
				patterns.push_back(Tcl_GetString(elems[j]));
		}
	};
	void check_simple() {
		if (regexp_flag || hierarchical_flag || nocase_flag || separator != "/" || of_objects) {
			log_error("%s got unexpected flags in simple mode\n", name);
		}
	}
	void check_simple_sep() {
		if (separator != "/")
			log_error("Only '/' accepted as separator");
	}
};

template <typename T>
void merge_or_init(const T& key, dict<T, BitSelection>& dst, const BitSelection& src) {
	if (dst.count(key) == 0) {
		dst[key] = src;
	} else {
		dst[key].merge(src);
	}
}

static int sdc_get_pins_cmd(ClientData data, Tcl_Interp *interp, int objc, Tcl_Obj* const objv[])
{
	auto* objects = (SdcObjects*)data;
	GetterOpts opts("get_pins", {"hierarchical", "hier", "regexp", "nocase", "hsc", "of_objects"});
	opts.parse(objc, objv);
	if (objects->collect_mode == SdcObjects::CollectMode::SimpleGetter)
		opts.check_simple();
	opts.check_simple_sep();

	MatchConfig config(opts.regexp_flag, opts.nocase_flag, opts.hierarchical_flag);
	std::vector<std::tuple<std::string, SdcObjects::CellPin, BitSelection>> resolved;
	const auto& pins = objects->design_pins;
	resolved = find_matching<SdcObjects::CellPin, decltype(pins)>(pins, config, opts.patterns, "pin");

	return getter_graph_node(TclCall{interp, objc, objv});
}

static int sdc_get_ports_cmd(ClientData data, Tcl_Interp *interp, int objc, Tcl_Obj* const objv[])
{
	auto* objects = (SdcObjects*)data;
	GetterOpts opts("get_ports", {"regexp", "nocase"});
	opts.parse(objc, objv);
	if (objects->collect_mode == SdcObjects::CollectMode::SimpleGetter)
		opts.check_simple();

	MatchConfig config(opts.regexp_flag, opts.nocase_flag, false);
	std::vector<std::tuple<std::string, Wire*, BitSelection>> resolved;
	const auto& ports = objects->design_ports;
	resolved = find_matching<Wire*, decltype(ports)>(ports, config, opts.patterns, "port");

	for (auto [name, wire, matching_bits] : resolved) {
		if (objects->collect_mode != SdcObjects::CollectMode::FullConstraint)
			merge_or_init(std::make_pair(name, wire), objects->constrained_ports, matching_bits);
	}

	// SILIMATE: remember what this node resolved to, for set_logic_zero/set_logic_one
	int ret = getter_graph_node(TclCall{interp, objc, objv});
	if (ret == TCL_OK)
		if (auto idx = magic_node_index(Tcl_GetStringResult(interp)))
			objects->port_nodes[*idx] = resolved;
	return ret;
}

// SILIMATE: set_logic_zero/set_logic_one, under sdc -constants: record the constant on
// every port bit the arguments resolve to (get_ports nodes, also nested in list), then
// record the call as unknown would
static void collect_logic_ports(Tcl_Interp* interp, SdcObjects* objects, const std::string& arg,
		State value, int depth = 0) {
	auto idx = magic_node_index(arg);
	if (!idx) {
		log_warning("set_logic argument '%s' is not a get_ports result; ignored.\n", arg);
		return;
	}
	if (objects->port_nodes.count(*idx)) {
		for (auto& [name, wire, bits] : objects->port_nodes.at(*idx))
			objects->logic_constants.push_back({wire, bits, value});
		return;
	}
	Tcl_Obj* calls = Tcl_GetVar2Ex(interp, "sdc_calls", nullptr, TCL_GLOBAL_ONLY);
	Tcl_Obj* call = nullptr;
	YS_Tcl_Size argc = 0;
	Tcl_Obj** argv = nullptr;
	if (depth < 16 && calls && Tcl_ListObjIndex(interp, calls, *idx, &call) == TCL_OK && call &&
			Tcl_ListObjGetElements(interp, call, &argc, &argv) == TCL_OK && argc > 0 &&
			std::string(Tcl_GetString(argv[0])) == "list") {
		for (YS_Tcl_Size i = 1; i < argc; i++)
			collect_logic_ports(interp, objects, Tcl_GetString(argv[i]), value, depth + 1);
		return;
	}
	log_warning("set_logic argument '%s' is not a get_ports result; ignored.\n", arg);
}

static int sdc_set_logic_cmd(ClientData data, Tcl_Interp *interp, int objc, Tcl_Obj* const objv[])
{
	auto* objects = (SdcObjects*)data;
	State value = std::string(Tcl_GetString(objv[0])) == "set_logic_one" ? State::S1 : State::S0;
	for (int i = 1; i < objc; i++) {
		YS_Tcl_Size argc = 0;
		Tcl_Obj** argv = nullptr;
		if (Tcl_ListObjGetElements(interp, objv[i], &argc, &argv) != TCL_OK)
			return TCL_ERROR;
		for (YS_Tcl_Size j = 0; j < argc; j++)
			collect_logic_ports(interp, objects, Tcl_GetString(argv[j]), value);
	}
	return redirect_unknown(TclCall{interp, objc, objv});
}

static int sdc_get_nets_cmd(ClientData data, Tcl_Interp *interp, int objc, Tcl_Obj* const objv[])
{
	auto* objects = (SdcObjects*)data;
	GetterOpts opts("get_nets", {"hierarchical", "hier", "regexp", "nocase", "hsc", "of_objects"});
	opts.parse(objc, objv);
	if (objects->collect_mode == SdcObjects::CollectMode::SimpleGetter)
		opts.check_simple();

	MatchConfig config(opts.regexp_flag, opts.nocase_flag, false);
	std::vector<std::tuple<std::string, Wire*, BitSelection>> resolved;
	const auto& ports = objects->design_nets;
	resolved = find_matching<Wire*, decltype(ports)>(ports, config, opts.patterns, "net");

	for (auto [name, wire, matching_bits] : resolved) {
		if (objects->collect_mode != SdcObjects::CollectMode::FullConstraint)
			merge_or_init(std::make_pair(name, wire), objects->constrained_nets, matching_bits);
	}

	return getter_graph_node(TclCall{interp, objc, objv});
}

class SDCInterpreter
{
private:
	Tcl_Interp* interp = nullptr;
public:
	std::unique_ptr<SdcObjects> objects;
	~SDCInterpreter() {
		if (interp)
			Tcl_DeleteInterp(interp);
	}
	static SDCInterpreter& get() {
		static SDCInterpreter instance;
		return instance;
	}
	Tcl_Interp* fresh_interp(Design* design) {
		if (interp)
			Tcl_DeleteInterp(interp);

		interp = Tcl_CreateInterp();
		// SILIMATE: use a wheel's bundled script library; without one, the stubs define unknown
		// themselves and the SDC needs only Tcl's built-in commands, so go on with a warning
		yosys_tcl_set_library(interp);
		if (Tcl_Init(interp)!=TCL_OK)
			log_warning("Tcl_Init() call failed - %s\n",Tcl_ErrnoMsg(Tcl_GetErrno()));

		objects = std::make_unique<SdcObjects>(design);
		objects->collect_mode = SdcObjects::CollectMode::SimpleGetter;
		Tcl_CreateObjCommand(interp, "get_pins", sdc_get_pins_cmd, (ClientData) objects.get(), NULL);
		Tcl_CreateObjCommand(interp, "get_nets", sdc_get_nets_cmd, (ClientData) objects.get(), NULL);
		Tcl_CreateObjCommand(interp, "get_ports", sdc_get_ports_cmd, (ClientData) objects.get(), NULL);
		return interp;
	}
};

// Also see TclPass
struct SdcPass : public Pass {
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    sdc [options] file\n");
		log("\n");
		log("Read the SDC file for the current design.\n");
		log("\n");
		log("    -dump\n");
		log("        Dump the referenced design objects.\n");
		log("\n");
		log("    -dump-graph\n");
		log("        Dump the uninterpreted call graph.\n");
		log("\n");
		log("    -keep_hierarchy\n");
		log("        Add keep_hierarchy attributes while retaining SDC validity.\n");
		log("\n");
		// SILIMATE
		log("    -constants\n");
		log("        Tie the top-level input ports that set_logic_zero and set_logic_one\n");
		log("        name (through get_ports, or a list of get_ports results) to those\n");
		log("        constants: every reader of such a port bit reads the constant instead,\n");
		log("        and the port itself stays. Run after proc.\n");
		log("\n");
		log("    -stubs <file>\n");
		log("        Evaluate this Tcl file before the SDC, e.g. to set the variables it\n");
		log("        reads. Can be given more than once.\n");
		log("\n");
	}
	SdcPass() : Pass("sdc", "Read an SDC file") { }
	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing SDC pass.\n");
		log_experimental("sdc");
		size_t argidx;
		bool dump_mode = false;
		bool dump_graph_mode = false;
		bool keep_hierarchy_mode = false;
		bool constants_mode = false; // SILIMATE
		std::vector<std::string> stubs_paths;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-dump") {
				dump_mode = true;
				continue;
			} else if (args[argidx] == "-dump-graph") {
				dump_graph_mode = true;
				continue;
			} else if (args[argidx] == "-keep_hierarchy") {
				keep_hierarchy_mode = true;
				continue;
			} else if (args[argidx] == "-constants") { // SILIMATE
				constants_mode = true;
				continue;
			} else if (args[argidx] == "-stubs" && argidx+1 < args.size()) {
				stubs_paths.push_back(args[++argidx]);
				continue;
			}
			break;
		}
		if (argidx >= args.size())
			log_cmd_error("Missing SDC file.\n");

		std::string sdc_path = args[argidx++];
		if (argidx < args.size())
			log_cmd_error("Unexpected extra positional argument %s after SDC file %s.\n", args[argidx], sdc_path);
		SDCInterpreter& sdc = SDCInterpreter::get();
		Tcl_Interp *interp = sdc.fresh_interp(design);
		Tcl_Preserve(interp);
		std::string stub_path = "+/sdc/graph-stubs.sdc";
		rewrite_filename(stub_path);
		if (Tcl_EvalFile(interp, stub_path.c_str()) != TCL_OK)
			log_cmd_error("SDC interpreter returned an error in stub preamble file: %s\n", Tcl_GetStringResult(interp));
		for (auto path : stubs_paths)
			if (Tcl_EvalFile(interp, path.c_str()) != TCL_OK)
				log_cmd_error("SDC interpreter returned an error in OpenSTA stub file %s: %s\n", path.c_str(), Tcl_GetStringResult(interp));
		// SILIMATE: after the stubs, so a stub file cannot shadow them
		if (constants_mode)
			for (auto cmd : {"set_logic_zero", "set_logic_one"})
				Tcl_CreateObjCommand(interp, cmd, sdc_set_logic_cmd, (ClientData) sdc.objects.get(), NULL);
		if (Tcl_EvalFile(interp, sdc_path.c_str()) != TCL_OK)
			log_cmd_error("SDC interpreter returned an error: %s\n", Tcl_GetStringResult(interp));
		if (dump_mode)
			sdc.objects->dump();
		if (keep_hierarchy_mode)
			sdc.objects->keep_hierarchy();
		if (constants_mode) // SILIMATE
			sdc.objects->tie_logic_constants();
		inspect_globals(interp, dump_graph_mode);
		Tcl_Release(interp);
	}
} SdcPass;

YOSYS_NAMESPACE_END
#endif
