/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *  Copyright (C) 2018  Ruben Undheim <ruben.undheim@gmail.com>
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
#include "frontends/verific/verific.h"
#include <stdlib.h>
#include <stdio.h>
#include <set>

#ifndef _WIN32
#  include <unistd.h>
#endif


USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct generate_port_decl_t {
	bool input, output;
	string portname;
	int index;
};

void generate(RTLIL::Design *design, const std::vector<std::string> &celltypes, const std::vector<generate_port_decl_t> &portdecls)
{
	std::set<RTLIL::IdString> found_celltypes;

	for (auto mod : design->modules())
	for (auto cell : mod->cells())
	{
		if (design->module(cell->type) != nullptr)
			continue;
		if (cell->type.begins_with("$") && !cell->type.begins_with("$__"))
			continue;
		for (auto &pattern : celltypes)
			if (patmatch(pattern.c_str(), RTLIL::unescape_id(cell->type).c_str()))
				found_celltypes.insert(cell->type);
	}

	for (auto &celltype : found_celltypes)
	{
		std::set<RTLIL::IdString> portnames;
		std::set<RTLIL::IdString> parameters;
		std::map<RTLIL::IdString, int> portwidths;
		log("Generate module for cell type %s:\n", celltype.c_str());

		for (auto mod : design->modules())
		for (auto cell : mod->cells())
			if (cell->type == celltype) {
				for (auto &conn : cell->connections()) {
					if (conn.first[0] != '$')
						portnames.insert(conn.first);
					portwidths[conn.first] = max(portwidths[conn.first], conn.second.size());
				}
				for (auto &para : cell->parameters)
					parameters.insert(para.first);
			}

		for (auto &decl : portdecls)
			if (decl.index > 0)
				portnames.insert(decl.portname);

		std::set<int> indices;
		for (int i = 0; i < int(portnames.size()); i++)
			indices.insert(i+1);

		std::vector<generate_port_decl_t> ports(portnames.size());

		for (auto &decl : portdecls)
			if (decl.index > 0) {
				portwidths[decl.portname] = max(portwidths[decl.portname], 1);
				portwidths[decl.portname] = max(portwidths[decl.portname], portwidths[stringf("$%d", decl.index)]);
				log("  port %d: %s [%d:0] %s\n", decl.index, decl.input ? decl.output ? "inout" : "input" : "output", portwidths[decl.portname]-1, RTLIL::id2cstr(decl.portname));
				if (indices.count(decl.index) > ports.size())
					log_error("Port index (%d) exceeds number of found ports (%d).\n", decl.index, int(ports.size()));
				if (indices.count(decl.index) == 0)
					log_error("Conflict on port index %d.\n", decl.index);
				indices.erase(decl.index);
				portnames.erase(decl.portname);
				ports[decl.index-1] = decl;
			}

		while (portnames.size() > 0) {
			RTLIL::IdString portname = *portnames.begin();
			for (auto &decl : portdecls)
				if (decl.index == 0 && patmatch(decl.portname.c_str(), RTLIL::unescape_id(portname).c_str())) {
					generate_port_decl_t d = decl;
					d.portname = portname.str();
					d.index = *indices.begin();
					log_assert(!indices.empty());
					indices.erase(d.index);
					ports[d.index-1] = d;
					portwidths[d.portname] = max(portwidths[d.portname], 1);
					log("  port %d: %s [%d:0] %s\n", d.index, d.input ? d.output ? "inout" : "input" : "output", portwidths[d.portname]-1, RTLIL::id2cstr(d.portname));
					goto found_matching_decl;
				}
			log_error("Can't match port %s.\n", RTLIL::id2cstr(portname));
		found_matching_decl:;
			portnames.erase(portname);
		}

		log_assert(indices.empty());

		RTLIL::Module *mod = new RTLIL::Module;
		mod->name = celltype;
		mod->attributes[ID::blackbox] = RTLIL::Const(1);
		design->add(mod);

		for (auto &decl : ports) {
			RTLIL::Wire *wire = mod->addWire(decl.portname, portwidths.at(decl.portname));
			wire->port_id = decl.index;
			wire->port_input = decl.input;
			wire->port_output = decl.output;
		}

		mod->fixup_ports();

		for (auto &para : parameters)
			log("  ignoring parameter %s.\n", RTLIL::id2cstr(para));

		log("  module %s created.\n", RTLIL::id2cstr(mod->name));
	}
}

// Return the "basic" type for an array item.
std::string basic_cell_type(const std::string celltype, int pos[3] = nullptr) {
	std::string basicType = celltype;
	if (celltype.compare(0, strlen("$array:"), "$array:") == 0) {
		int pos_idx = celltype.find_first_of(':');
		int pos_num = celltype.find_first_of(':', pos_idx + 1);
		int pos_type = celltype.find_first_of(':', pos_num + 1);
		basicType = celltype.substr(pos_type + 1);
		if (pos != nullptr) {
			pos[0] = pos_idx;
			pos[1] = pos_num;
			pos[2] = pos_type;
		}
	}
	return basicType;
}

// A helper struct for expanding a module's interface connections in expand_module
struct IFExpander
{
	IFExpander (RTLIL::Design &design, RTLIL::Module &m)
		: module(m), has_interfaces_not_found(false)
	{
		// Keep track of all derived interfaces available in the current
		// module in 'interfaces_in_module':
		for (auto cell : module.cells()) {
			if(!cell->get_bool_attribute(ID::is_interface))
				continue;

			interfaces_in_module[cell->name] = design.module(cell->type);
		}
	}

	RTLIL::Module                          &module;
	dict<RTLIL::IdString, RTLIL::Module*>   interfaces_in_module;

	bool                                    has_interfaces_not_found;
	std::vector<RTLIL::IdString>            connections_to_remove;
	std::vector<RTLIL::IdString>            connections_to_add_name;
	std::vector<RTLIL::SigSpec>             connections_to_add_signal;
	dict<RTLIL::IdString, RTLIL::Module*>   interfaces_to_add_to_submodule;
	dict<RTLIL::IdString, RTLIL::IdString>  modports_used_in_submodule;

	// Reset the per-cell state
	void start_cell()
	{
		has_interfaces_not_found = false;
		connections_to_remove.clear();
		connections_to_add_name.clear();
		connections_to_add_signal.clear();
		interfaces_to_add_to_submodule.clear();
		modports_used_in_submodule.clear();
	}

	// Set has_interfaces_not_found if there are pending interfaces that
	// haven't been found yet (and might be found in the future). Print a
	// warning if we've already gone over all the cells in the module.
	void on_missing_interface(RTLIL::IdString interface_name)
	{
		// If there are cells that haven't yet been processed, maybe
		// we'll find this interface in the future.
		if (module.get_bool_attribute(ID::cells_not_processed)) {
			has_interfaces_not_found = true;
			return;
		}

		// Otherwise, we have already gone over all cells in this
		// module and the interface has still not been found. Warn
		// about it and don't set has_interfaces_not_found (to avoid a
		// loop).
		log_warning("Could not find interface instance for `%s' in `%s'\n",
			    log_id(interface_name), log_id(&module));
	}

	// Handle an interface connection from the module
	void on_interface(RTLIL::Module        &submodule,
	                  RTLIL::IdString       conn_name,
	                  const RTLIL::SigSpec &conn_signals)
	{
		// Check if the connected wire is a potential interface in the parent module
		std::string interface_name_str = conn_signals[0].wire->name.str();
		// Strip the prefix '$dummywireforinterface' from the dummy wire to get the name
		interface_name_str.replace(0,23,"");
		interface_name_str = "\\" + interface_name_str;
		RTLIL::IdString interface_name = interface_name_str;

		// If 'interfaces' in the cell have not be been handled yet, we aren't
		// ready to derive the sub-module either
		if (!module.get_bool_attribute(ID::interfaces_replaced_in_module)) {
			on_missing_interface(interface_name);
			return;
		}

		// Check if the interface instance is present in module. Interface
		// instances may either have the plain name or the name appended with
		// '_inst_from_top_dummy'. Check for both of them here
		int nexactmatch = interfaces_in_module.count(interface_name) > 0;
		std::string interface_name_str2 =  interface_name_str + "_inst_from_top_dummy";
		RTLIL::IdString interface_name2 = interface_name_str2;
		int nmatch2 = interfaces_in_module.count(interface_name2) > 0;

		// If we can't find either name, this is a missing interface.
		if (! (nexactmatch || nmatch2)) {
			on_missing_interface(interface_name);
			return;
		}

		if (nexactmatch != 0) // Choose the one with the plain name if it exists
			interface_name2 = interface_name;

		RTLIL::Module *mod_replace_ports = interfaces_in_module.at(interface_name2);

		// Go over all wires in interface, and add replacements to lists.
		for (auto mod_wire : mod_replace_ports->wires()) {
			std::string signal_name1 = conn_name.str() + "." + log_id(mod_wire->name);
			std::string signal_name2 = interface_name.str() + "." + log_id(mod_wire);
			connections_to_add_name.push_back(RTLIL::IdString(signal_name1));
			if(module.wire(signal_name2) == nullptr) {
				log_error("Could not find signal '%s' in '%s'\n",
					  signal_name2.c_str(), log_id(module.name));
			}
			else {
				RTLIL::Wire *wire_in_parent = module.wire(signal_name2);
				connections_to_add_signal.push_back(wire_in_parent);
			}
		}
		connections_to_remove.push_back(conn_name);
		interfaces_to_add_to_submodule[conn_name] = interfaces_in_module.at(interface_name2);

		// Find if the sub-module has set a modport for the current interface
		// connection. Add any modports to a dict which will be passed to
		// AstModule::derive
		string modport_name = submodule.wire(conn_name)->get_string_attribute(ID::interface_modport);
		if (!modport_name.empty()) {
			modports_used_in_submodule[conn_name] = "\\" + modport_name;
		}
	}

	// Handle a single connection from the module, making a note to expand
	// it if it's an interface connection.
	void on_connection(RTLIL::Module        &submodule,
	                   RTLIL::IdString       conn_name,
	                   const RTLIL::SigSpec &conn_signals)
	{
		// Check if the connection is present as an interface in the sub-module's port list
		const RTLIL::Wire *wire = submodule.wire(conn_name);
		if (!wire || !wire->get_bool_attribute(ID::is_interface))
			return;

		// If the connection looks like an interface, handle it.
		const auto &bits = conn_signals;
		if (bits.size() == 1 && bits[0].wire->get_bool_attribute(ID::is_interface))
			on_interface(submodule, conn_name, conn_signals);
	}

	// Iterate over the connections in a cell, tracking any interface
	// connections
	void visit_connections(const RTLIL::Cell &cell,
			       RTLIL::Module     &submodule)
	{
		for (const auto &conn : cell.connections()) {
			on_connection(submodule, conn.first, conn.second);
		}
	}

	// Add/remove connections to the cell as necessary, replacing any SV
	// interface port connection with the individual signal connections.
	void rewrite_interface_connections(RTLIL::Cell &cell) const
	{
		for(unsigned int i=0;i<connections_to_add_name.size();i++) {
			cell.connections_[connections_to_add_name[i]] = connections_to_add_signal[i];
		}
		// Remove the connection for the interface itself:
		for(unsigned int i=0;i<connections_to_remove.size();i++) {
			cell.connections_.erase(connections_to_remove[i]);
		}
	}
};

// Get a module needed by a cell, either by deriving an abstract module or by
// loading one from a directory in libdirs.
//
// If the module can't be found and check is true then exit with an error
// message. Otherwise, return a pointer to the module if we derived or loaded
// something. or null otherwise (the module should be blackbox or we couldn't
// find it and check is not set).
RTLIL::Module *get_module(RTLIL::Design                  &design,
                          RTLIL::Cell                    &cell,
                          RTLIL::Module                  &parent,
                          bool                            check,
                          const std::vector<std::string> &libdirs)
{
	std::string cell_type = cell.type.str();
	RTLIL::Module *abs_mod = design.module("$abstract" + cell_type);
	if (abs_mod) {
		cell.type = abs_mod->derive(&design, cell.parameters);
		cell.parameters.clear();
		RTLIL::Module *mod = design.module(cell.type);
		log_assert(mod);
		return mod;
	}

	// If the cell type starts with '$' and isn't '$abstract', we should
	// treat it as a black box and skip.
	if (cell_type[0] == '$')
		return nullptr;

	for (auto &dir : libdirs) {
		static const vector<pair<string, string>> extensions_list =
			{
			 {".v", "verilog"},
			 {".sv", "verilog -sv"},
			 {".il", "rtlil"}
			};

		for (auto &ext : extensions_list) {
			std::string filename = dir + "/" + RTLIL::unescape_id(cell.type) + ext.first;
			if (!check_file_exists(filename))
				continue;

			Frontend::frontend_call(&design, NULL, filename, ext.second);
			RTLIL::Module *mod = design.module(cell.type);
			if (!mod)
				log_error("File `%s' from libdir does not declare module `%s'.\n",
				          filename.c_str(), cell_type.c_str());
			return mod;
		}
	}

	// We couldn't find the module anywhere. Complain if check is set.
	if (check)
		log_error("Module `%s' referenced in module `%s' in cell `%s' is not part of the design.\n",
		          cell_type.c_str(), parent.name.c_str(), cell.name.c_str());

	return nullptr;
}

// Try to read an IdString as a numbered connection name ("$123" or similar),
// writing the result to dst. If the string isn't of the right format, ignore
// dst and return false.
bool read_id_num(RTLIL::IdString str, int *dst)
{
	log_assert(dst);

	const char *c_str = str.c_str();
	if (c_str[0] != '$' || !('0' <= c_str[1] && c_str[1] <= '9'))
		return false;

	*dst = atoi(c_str + 1);
	return true;
}

// Check that the connections on the cell match those that are defined
// on the type: each named connection should match the name of a port
// and each positional connection should have an index smaller than
// the number of ports.
//
// Also do the same checks on the specified parameters.
void check_cell_connections(const RTLIL::Module &module, RTLIL::Cell &cell, RTLIL::Module &mod)
{
	int id;
	for (auto &conn : cell.connections()) {
		if (read_id_num(conn.first, &id)) {
			if (id <= 0 || id > GetSize(mod.ports))
				log_error("Module `%s' referenced in module `%s' in cell `%s' "
				          "has only %d ports, requested port %d.\n",
				          log_id(cell.type), log_id(&module), log_id(&cell),
				          GetSize(mod.ports), id);
			continue;
		}

		const RTLIL::Wire* wire = mod.wire(conn.first);
		if (!wire || wire->port_id == 0) {
			log_error("Module `%s' referenced in module `%s' in cell `%s' "
			          "does not have a port named '%s'.\n",
			          log_id(cell.type), log_id(&module), log_id(&cell),
			          log_id(conn.first));
		}
	}
	for (auto &param : cell.parameters) {
		if (read_id_num(param.first, &id)) {
			if (id <= 0 || id > GetSize(mod.avail_parameters))
				log_error("Module `%s' referenced in module `%s' in cell `%s' "
				          "has only %d parameters, requested parameter %d.\n",
				          log_id(cell.type), log_id(&module), log_id(&cell),
				          GetSize(mod.avail_parameters), id);
			continue;
		}

		if (mod.avail_parameters.count(param.first) == 0 &&
		    param.first[0] != '$' &&
		    strchr(param.first.c_str(), '.') == NULL) {
			log_error("Module `%s' referenced in module `%s' in cell `%s' "
			          "does not have a parameter named '%s'.\n",
			          log_id(cell.type), log_id(&module), log_id(&cell),
			          log_id(param.first));
		}
	}
}

bool expand_module(RTLIL::Design *design, RTLIL::Module *module, bool flag_check, bool flag_simcheck, bool flag_smtcheck,
		   std::vector<std::string> &libdirs)
{
	bool did_something = false;
	std::map<RTLIL::Cell*, std::pair<int, int>> array_cells;
	std::string filename;

	bool has_interface_ports = false;

	// If any of the ports are actually interface ports, we will always need to
	// reprocess the module:
	if(!module->get_bool_attribute(ID::interfaces_replaced_in_module)) {
		for (auto wire : module->wires()) {
			if ((wire->port_input || wire->port_output) && wire->get_bool_attribute(ID::is_interface))
				has_interface_ports = true;
		}
	}

	IFExpander if_expander(*design, *module);

	for (auto cell : module->cells())
	{
		if_expander.start_cell();

		if (cell->type.begins_with("$array:")) {
			int pos[3];
			basic_cell_type(cell->type.str(), pos);
			int pos_idx = pos[0];
			int pos_num = pos[1];
			int pos_type = pos[2];
			int idx = atoi(cell->type.substr(pos_idx + 1, pos_num).c_str());
			int num = atoi(cell->type.substr(pos_num + 1, pos_type).c_str());
			array_cells[cell] = std::pair<int, int>(idx, num);
			cell->type = cell->type.substr(pos_type + 1);
		}

		RTLIL::Module *mod = design->module(cell->type);
		if (!mod)
		{
			mod = get_module(*design, *cell, *module, flag_check || flag_simcheck || flag_smtcheck, libdirs);

			// If we still don't have a module, treat the cell as a black box and skip
			// it. Otherwise, we either loaded or derived something so should set the
			// did_something flag before returning (to ensure we come back and expand
			// the thing we just loaded).
			if (mod)
				did_something = true;

			continue;
		}

		log_assert(mod);

		// Go over all connections and check if any of them are SV
		// interfaces.
		if_expander.visit_connections(*cell, *mod);

		if (flag_check || flag_simcheck || flag_smtcheck)
			check_cell_connections(*module, *cell, *mod);

		if (mod->get_blackbox_attribute()) {
			if (flag_simcheck || (flag_smtcheck && !mod->get_bool_attribute(ID::smtlib2_module)))
				log_error("Module `%s' referenced in module `%s' in cell `%s' is a blackbox/whitebox module.\n",
						cell->type.c_str(), module->name.c_str(), cell->name.c_str());
			continue;
		}

		// If interface instances not yet found, skip cell for now, and say we did something, so that we will return back here:
		if(if_expander.has_interfaces_not_found) {
			did_something = true; // waiting for interfaces to be handled
			continue;
		}

		if_expander.rewrite_interface_connections(*cell);

		// If there are no overridden parameters AND not interfaces, then we can use the existing module instance as the type
		// for the cell:
		if (cell->parameters.size() == 0 &&
		    (if_expander.interfaces_to_add_to_submodule.size() == 0 ||
		     !(cell->get_bool_attribute(ID::module_not_derived)))) {
			// If the cell being processed is an the interface instance itself, go down to "handle_interface_instance:",
			// so that the signals of the interface are added to the parent module.
			if (mod->get_bool_attribute(ID::is_interface)) {
				goto handle_interface_instance;
			}
			continue;
		}

		cell->type = mod->derive(design,
					 cell->parameters,
					 if_expander.interfaces_to_add_to_submodule,
					 if_expander.modports_used_in_submodule);
		cell->parameters.clear();
		did_something = true;

		handle_interface_instance:

			// We add all the signals of the interface explicitly to the parent module. This is always needed when we encounter
			// an interface instance:
			if (mod->get_bool_attribute(ID::is_interface) && cell->get_bool_attribute(ID::module_not_derived)) {
				cell->set_bool_attribute(ID::is_interface);
				RTLIL::Module *derived_module = design->module(cell->type);
				if_expander.interfaces_in_module[cell->name] = derived_module;
				did_something = true;
			}
		// We clear 'module_not_derived' such that we will not rederive the cell again (needed when there are interfaces connected to the cell)
		cell->attributes.erase(ID::module_not_derived);
	}
	// Clear the attribute 'cells_not_processed' such that it can be known that we
	// have been through all cells at least once, and that we can know whether
	// to flag an error because of interface instances not found:
	module->attributes.erase(ID::cells_not_processed);


	// If any interface instances or interface ports were found in the module, we need to rederive it completely:
	if ((if_expander.interfaces_in_module.size() > 0 || has_interface_ports) && !module->get_bool_attribute(ID::interfaces_replaced_in_module)) {
		module->expand_interfaces(design, if_expander.interfaces_in_module);
		return did_something;
	}

	// Now that modules have been derived, we may want to reprocess this
	// module given the additional available context.
	if (module->reprocess_if_necessary(design))
		return true;

	for (auto &it : array_cells)
	{
		RTLIL::Cell *cell = it.first;
		int idx = it.second.first, num = it.second.second;

		if (design->module(cell->type) == nullptr)
			log_error("Array cell `%s.%s' of unknown type `%s'.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));

		RTLIL::Module *mod = design->module(cell->type);

		for (auto &conn : cell->connections_) {
			int conn_size = conn.second.size();
			RTLIL::IdString portname = conn.first;
			if (portname.begins_with("$")) {
				int port_id = atoi(portname.substr(1).c_str());
				for (auto wire : mod->wires())
					if (wire->port_id == port_id) {
						portname = wire->name;
						break;
					}
			}
			if (mod->wire(portname) == nullptr)
				log_error("Array cell `%s.%s' connects to unknown port `%s'.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(conn.first));
			int port_size = mod->wire(portname)->width;
			if (conn_size == port_size || conn_size == 0)
				continue;
			if (conn_size != port_size*num)
				log_error("Array cell `%s.%s' has invalid port vs. signal size for port `%s'.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(conn.first));
			conn.second = conn.second.extract(port_size*idx, port_size);
		}
	}

	return did_something;
}

void hierarchy_worker(RTLIL::Design *design, std::set<RTLIL::Module*, IdString::compare_ptr_by_name<Module>> &used, RTLIL::Module *mod, int indent)
{
	if (used.count(mod) > 0)
		return;

	if (indent == 0)
		log("Top module:  %s\n", mod->name.c_str());
	else if (!mod->get_blackbox_attribute())
		log("Used module: %*s%s\n", indent, "", mod->name.c_str());
	used.insert(mod);

	for (auto cell : mod->cells()) {
		std::string celltype = cell->type.str();
		if (celltype.compare(0, strlen("$array:"), "$array:") == 0)
			celltype = basic_cell_type(celltype);
		if (design->module(celltype))
			hierarchy_worker(design, used, design->module(celltype), indent+4);
	}
}

void hierarchy_clean(RTLIL::Design *design, RTLIL::Module *top, bool purge_lib)
{
	std::set<RTLIL::Module*, IdString::compare_ptr_by_name<Module>> used;
	hierarchy_worker(design, used, top, 0);

	std::vector<RTLIL::Module*> del_modules;
	for (auto mod : design->modules())
		if (used.count(mod) == 0)
			del_modules.push_back(mod);
		else {
			// Now all interface ports must have been exploded, and it is hence
			// safe to delete all of the remaining dummy interface ports:
			pool<RTLIL::Wire*> del_wires;
			for(auto wire : mod->wires()) {
				if ((wire->port_input || wire->port_output) && wire->get_bool_attribute(ID::is_interface)) {
					del_wires.insert(wire);
				}
			}
			if (del_wires.size() > 0) {
				mod->remove(del_wires);
				mod->fixup_ports();
			}
		}

	int del_counter = 0;
	for (auto mod : del_modules) {
		if (!purge_lib && mod->get_blackbox_attribute())
			continue;
		log("Removing unused module `%s'.\n", mod->name.c_str());
		design->remove(mod);
		del_counter++;
	}

	log("Removed %d unused modules.\n", del_counter);
}

bool set_keep_print(std::map<RTLIL::Module*, bool> &cache, RTLIL::Module *mod)
{
	if (cache.count(mod) == 0)
		for (auto c : mod->cells()) {
			RTLIL::Module *m = mod->design->module(c->type);
			if ((m != nullptr && set_keep_print(cache, m)) || c->type == ID($print))
				return cache[mod] = true;
		}
	return cache[mod];
}

bool set_keep_assert(std::map<RTLIL::Module*, bool> &cache, RTLIL::Module *mod)
{
	if (cache.count(mod) == 0)
		for (auto c : mod->cells()) {
			RTLIL::Module *m = mod->design->module(c->type);
			if ((m != nullptr && set_keep_assert(cache, m)) || c->type.in(ID($check), ID($assert), ID($assume), ID($live), ID($fair), ID($cover)))
				return cache[mod] = true;
		}
	return cache[mod];
}

int find_top_mod_score(Design *design, Module *module, dict<Module*, int> &db)
{
	if (db.count(module) == 0) {
		int score = 0;
		db[module] = 0;
		for (auto cell : module->cells()) {
			std::string celltype = cell->type.str();
			// Is this an array instance
			if (celltype.compare(0, strlen("$array:"), "$array:") == 0)
				celltype = basic_cell_type(celltype);
			// Is this cell a module instance?
			auto instModule = design->module(celltype);
			// If there is no instance for this, issue a warning.
			if (instModule != nullptr) {
				score = max(score, find_top_mod_score(design, instModule, db) + 1);
			}
		}
		db[module] = score;
	}
	return db.at(module);
}

RTLIL::Module *check_if_top_has_changed(Design *design, Module *top_mod)
{
	if(top_mod != NULL && top_mod->get_bool_attribute(ID::initial_top))
		return top_mod;
	else {
		for (auto mod : design->modules()) {
			if (mod->get_bool_attribute(ID::top)) {
				return mod;
			}
		}
	}
	return NULL;
}

// Find a matching wire for an implicit port connection; traversing generate block scope
RTLIL::Wire *find_implicit_port_wire(Module *module, Cell *cell, const std::string& port)
{
	const std::string &cellname = cell->name.str();
	size_t idx = cellname.size();
	while ((idx = cellname.find_last_of('.', idx-1)) != std::string::npos) {
		Wire *found = module->wire(cellname.substr(0, idx+1) + port.substr(1));
		if (found != nullptr)
			return found;
	}
	return module->wire(port);
}

struct HierarchyPass : public Pass {
	HierarchyPass() : Pass("hierarchy", "check, expand and clean up design hierarchy") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    hierarchy [-check] [-top <module>]\n");
		log("    hierarchy -generate <cell-types> <port-decls>\n");
		log("\n");
		log("In parametric designs, a module might exists in several variations with\n");
		log("different parameter values. This pass looks at all modules in the current\n");
		log("design and re-runs the language frontends for the parametric modules as\n");
		log("needed. It also resolves assignments to wired logic data types (wand/wor),\n");
		log("resolves positional module parameters, unrolls array instances, and more.\n");
		log("\n");
		log("    -check\n");
		log("        also check the design hierarchy. this generates an error when\n");
		log("        an unknown module is used as cell type.\n");
		log("\n");
		log("    -simcheck\n");
		log("        like -check, but also throw an error if blackbox modules are\n");
		log("        instantiated, and throw an error if the design has no top module.\n");
		log("\n");
		log("    -smtcheck\n");
		log("        like -simcheck, but allow smtlib2_module modules.\n");
		log("\n");
		log("    -purge_lib\n");
		log("        by default the hierarchy command will not remove library (blackbox)\n");
		log("        modules. use this option to also remove unused blackbox modules.\n");
		log("\n");
		log("    -libdir <directory>\n");
		log("        search for files named <module_name>.v in the specified directory\n");
		log("        for unknown modules and automatically run read_verilog for each\n");
		log("        unknown module.\n");
		log("\n");
		log("    -keep_positionals\n");
		log("        per default this pass also converts positional arguments in cells\n");
		log("        to arguments using port names. This option disables this behavior.\n");
		log("\n");
		log("    -keep_portwidths\n");
		log("        per default this pass adjusts the port width on cells that are\n");
		log("        module instances when the width does not match the module port. This\n");
		log("        option disables this behavior.\n");
		log("\n");
		log("    -nodefaults\n");
		log("        do not resolve input port default values\n");
		log("\n");
		log("    -nokeep_prints\n");
		log("        per default this pass sets the \"keep\" attribute on all modules\n");
		log("        that directly or indirectly display text on the terminal.\n");
		log("        This option disables this behavior.\n");
		log("\n");
		log("    -nokeep_asserts\n");
		log("        per default this pass sets the \"keep\" attribute on all modules\n");
		log("        that directly or indirectly contain one or more formal properties.\n");
		log("        This option disables this behavior.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified top module to build the design hierarchy. Modules\n");
		log("        outside this tree (unused modules) are removed.\n");
		log("\n");
		log("        when the -top option is used, the 'top' attribute will be set on the\n");
		log("        specified top module. otherwise a module with the 'top' attribute set\n");
		log("        will implicitly be used as top module, if such a module exists.\n");
		log("\n");
		log("    -auto-top\n");
		log("        automatically determine the top of the design hierarchy and mark it.\n");
		log("\n");
		log("    -chparam name value \n");
		log("       elaborate the top module using this parameter value. Modules on which\n");
		log("       this parameter does not exist may cause a warning message to be output.\n");
		log("       This option can be specified multiple times to override multiple\n");
		log("       parameters. String values must be passed in double quotes (\").\n");
		log("\n");
		log("In -generate mode this pass generates blackbox modules for the given cell\n");
		log("types (wildcards supported). For this the design is searched for cells that\n");
		log("match the given types and then the given port declarations are used to\n");
		log("determine the direction of the ports. The syntax for a port declaration is:\n");
		log("\n");
		log("    {i|o|io}[@<num>]:<portname>\n");
		log("\n");
		log("Input ports are specified with the 'i' prefix, output ports with the 'o'\n");
		log("prefix and inout ports with the 'io' prefix. The optional <num> specifies\n");
		log("the position of the port in the parameter list (needed when instantiated\n");
		log("using positional arguments). When <num> is not specified, the <portname> can\n");
		log("also contain wildcard characters.\n");
		log("\n");
		log("This pass ignores the current selection and always operates on all modules\n");
		log("in the current design.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing HIERARCHY pass (managing design hierarchy).\n");

		bool flag_check = false;
		bool flag_simcheck = false;
		bool flag_smtcheck = false;
		bool purge_lib = false;
		RTLIL::Module *top_mod = NULL;
		std::string load_top_mod;
		std::vector<std::string> libdirs;

		bool auto_top_mode = false;
		bool generate_mode = false;
		bool keep_positionals = false;
		bool keep_portwidths = false;
		bool nodefaults = false;
		bool nokeep_prints = false;
		bool nokeep_asserts = false;
		std::vector<std::string> generate_cells;
		std::vector<generate_port_decl_t> generate_ports;
		std::map<std::string, std::string> parameters;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-generate" && !flag_check && !flag_simcheck && !flag_smtcheck && !top_mod) {
				generate_mode = true;
				log("Entering generate mode.\n");
				while (++argidx < args.size()) {
					const char *p = args[argidx].c_str();
					generate_port_decl_t decl;
					if (p[0] == 'i' && p[1] == 'o')
						decl.input = true, decl.output = true, p += 2;
					else if (*p == 'i')
						decl.input = true, decl.output = false, p++;
					else if (*p == 'o')
						decl.input = false, decl.output = true, p++;
					else
						goto is_celltype;
					if (*p == '@') {
						char *endptr;
						decl.index = strtol(++p, &endptr, 10);
						if (decl.index < 1)
							goto is_celltype;
						p = endptr;
					} else
						decl.index = 0;
					if (*(p++) != ':')
						goto is_celltype;
					if (*p == 0)
						goto is_celltype;
					decl.portname = p;
					log("Port declaration: %s", decl.input ? decl.output ? "inout" : "input" : "output");
					if (decl.index >= 1)
						log(" [at position %d]", decl.index);
					log(" %s\n", decl.portname.c_str());
					generate_ports.push_back(decl);
					continue;
				is_celltype:
					log("Celltype: %s\n", args[argidx].c_str());
					generate_cells.push_back(RTLIL::unescape_id(args[argidx]));
				}
				continue;
			}
			if (args[argidx] == "-check") {
				flag_check = true;
				continue;
			}
			if (args[argidx] == "-simcheck") {
				flag_simcheck = true;
				continue;
			}
			if (args[argidx] == "-smtcheck") {
				flag_smtcheck = true;
				continue;
			}
			if (args[argidx] == "-purge_lib") {
				purge_lib = true;
				continue;
			}
			if (args[argidx] == "-keep_positionals") {
				keep_positionals = true;
				continue;
			}
			if (args[argidx] == "-keep_portwidths") {
				keep_portwidths = true;
				continue;
			}
			if (args[argidx] == "-nodefaults") {
				nodefaults = true;
				continue;
			}
			if (args[argidx] == "-nokeep_prints") {
				nokeep_prints = true;
				continue;
			}
			if (args[argidx] == "-nokeep_asserts") {
				nokeep_asserts = true;
				continue;
			}
			if (args[argidx] == "-libdir" && argidx+1 < args.size()) {
				libdirs.push_back(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-top") {
				if (++argidx >= args.size())
					log_cmd_error("Option -top requires an additional argument!\n");
				load_top_mod = args[argidx];
				continue;
			}
			if (args[argidx] == "-auto-top") {
				auto_top_mode = true;
				continue;
			}
			if (args[argidx] == "-chparam"  && argidx+2 < args.size()) {
				const std::string &key = args[++argidx];
				const std::string &value = args[++argidx];
				auto r = parameters.emplace(key, value);
				if (!r.second) {
					log_warning("-chparam %s already specified: overwriting.\n", key.c_str());
					r.first->second = value;
				}
				continue;
			}
			break;
		}
		extra_args(args, argidx, design, false);

		if (!load_top_mod.empty())
		{
			IdString top_name = RTLIL::escape_id(load_top_mod);
			IdString abstract_id = "$abstract" + RTLIL::escape_id(load_top_mod);
			top_mod = design->module(top_name);

			dict<RTLIL::IdString, RTLIL::Const> top_parameters;
			if ((top_mod == nullptr && design->module(abstract_id)) || top_mod != nullptr) {
				for (auto &para : parameters) {
					SigSpec sig_value;
					if (!RTLIL::SigSpec::parse(sig_value, NULL, para.second))
						log_cmd_error("Can't decode value '%s'!\n", para.second.c_str());
					top_parameters[RTLIL::escape_id(para.first)] = sig_value.as_const();
				}
			}

			if (top_mod == nullptr && design->module(abstract_id))
				top_mod = design->module(design->module(abstract_id)->derive(design, top_parameters));
			else if (top_mod != nullptr && !top_parameters.empty())
				top_mod = design->module(top_mod->derive(design, top_parameters));

			if (top_mod != nullptr && top_mod->name != top_name) {
				Module *m = top_mod->clone();
				m->name = top_name;
				Module *old_mod = design->module(top_name);
				if (old_mod)
					design->remove(old_mod);
				design->add(m);
				top_mod = m;
			}
		}

		bool verific_mod = false;
#ifdef YOSYS_ENABLE_VERIFIC
		verific_mod = verific_import_pending;
#endif

		if (top_mod == nullptr && !load_top_mod.empty()) {
#ifdef YOSYS_ENABLE_VERIFIC
			if (verific_import_pending) {
				load_top_mod = verific_import(design, parameters, load_top_mod);
				top_mod = design->module(RTLIL::escape_id(load_top_mod));
			}
#endif
			if (top_mod == NULL)
				log_cmd_error("Module `%s' not found!\n", load_top_mod.c_str());
		} else {
#ifdef YOSYS_ENABLE_VERIFIC
			if (verific_import_pending)
				verific_import(design, parameters, std::string());
#endif
		}

		if (generate_mode) {
			generate(design, generate_cells, generate_ports);
			return;
		}

		log_push();

		if (top_mod == nullptr)
			for (auto mod : design->modules())
				if (mod->get_bool_attribute(ID::top)) {
					log("Attribute `top' found on module `%s'. Setting top module to %s.\n", log_id(mod), log_id(mod));
					top_mod = mod;
				}

		if (top_mod == nullptr)
		{
			std::vector<IdString> abstract_ids;
			for (auto module : design->modules())
				if (module->name.begins_with("$abstract"))
					abstract_ids.push_back(module->name);
			for (auto abstract_id : abstract_ids)
				design->module(abstract_id)->derive(design, {});
			for (auto abstract_id : abstract_ids)
				design->remove(design->module(abstract_id));
		}

		if (top_mod == nullptr && auto_top_mode) {
			log_header(design, "Finding top of design hierarchy..\n");
			dict<Module*, int> db;
			for (Module *mod : design->selected_modules()) {
				int score = find_top_mod_score(design, mod, db);
				log("root of %3d design levels: %-20s\n", score, log_id(mod));
				if (!top_mod || score > db[top_mod])
					top_mod = mod;
			}
			if (top_mod != nullptr)
				log("Automatically selected %s as design top module.\n", log_id(top_mod));
		}

		if (top_mod != nullptr && top_mod->name.begins_with("$abstract")) {
			IdString top_name = top_mod->name.substr(strlen("$abstract"));

			dict<RTLIL::IdString, RTLIL::Const> top_parameters;
			for (auto &para : parameters) {
				SigSpec sig_value;
				if (!RTLIL::SigSpec::parse(sig_value, NULL, para.second))
					log_cmd_error("Can't decode value '%s'!\n", para.second.c_str());
				top_parameters[RTLIL::escape_id(para.first)] = sig_value.as_const();
			}

			top_mod = design->module(top_mod->derive(design, top_parameters));

			if (top_mod != nullptr && top_mod->name != top_name) {
				Module *m = top_mod->clone();
				m->name = top_name;
				Module *old_mod = design->module(top_name);
				if (old_mod)
					design->remove(old_mod);
				design->add(m);
				top_mod = m;
			}
		}

		if ((flag_simcheck || flag_smtcheck) && top_mod == nullptr)
			log_error("Design has no top module.\n");

		if (top_mod != NULL) {
			for (auto mod : design->modules())
				if (mod == top_mod)
					mod->attributes[ID::initial_top] = RTLIL::Const(1);
				else
					mod->attributes.erase(ID::initial_top);
		}

		bool did_something = true;
		while (did_something)
		{
			did_something = false;

			std::set<RTLIL::Module*, IdString::compare_ptr_by_name<Module>> used_modules;
			if (top_mod != NULL) {
				log_header(design, "Analyzing design hierarchy..\n");
				hierarchy_worker(design, used_modules, top_mod, 0);
			} else {
				for (auto mod : design->modules())
					used_modules.insert(mod);
			}

			for (auto module : used_modules) {
				if (expand_module(design, module, flag_check, flag_simcheck, flag_smtcheck, libdirs))
					did_something = true;
			}


			// The top module might have changed if interface instances have been detected in it:
			RTLIL::Module *tmp_top_mod = check_if_top_has_changed(design, top_mod);
			if (tmp_top_mod != NULL) {
				if (tmp_top_mod != top_mod){
					top_mod = tmp_top_mod;
					top_mod->attributes[ID::initial_top] = RTLIL::Const(1);
					did_something = true;
				}
			}

			// Delete modules marked as 'to_delete':
			std::vector<RTLIL::Module *> modules_to_delete;
			for(auto mod : design->modules()) {
				if (mod->get_bool_attribute(ID::to_delete)) {
					modules_to_delete.push_back(mod);
				}
			}
			for(size_t i=0; i<modules_to_delete.size(); i++) {
				design->remove(modules_to_delete[i]);
			}
		}


		if (top_mod != NULL) {
			log_header(design, "Analyzing design hierarchy..\n");
			hierarchy_clean(design, top_mod, purge_lib);
		}

		if (top_mod != NULL) {
			for (auto mod : design->modules()) {
				if (mod == top_mod)
					mod->attributes[ID::top] = RTLIL::Const(1);
				else
					mod->attributes.erase(ID::top);
				mod->attributes.erase(ID::initial_top);
			}
		}

		if (!nokeep_prints) {
			std::map<RTLIL::Module*, bool> cache;
			for (auto mod : design->modules())
				if (set_keep_print(cache, mod)) {
					log("Module %s directly or indirectly displays text -> setting \"keep\" attribute.\n", log_id(mod));
					mod->set_bool_attribute(ID::keep);
				}
		}

		if (!nokeep_asserts) {
			std::map<RTLIL::Module*, bool> cache;
			for (auto mod : design->modules())
				if (set_keep_assert(cache, mod)) {
					log("Module %s directly or indirectly contains formal properties -> setting \"keep\" attribute.\n", log_id(mod));
					mod->set_bool_attribute(ID::keep);
				}
		}

		if (!keep_positionals)
		{
			std::set<RTLIL::Module*> pos_mods;
			std::map<std::pair<RTLIL::Module*,int>, RTLIL::IdString> pos_map;
			std::vector<std::pair<RTLIL::Module*,RTLIL::Cell*>> pos_work;

			for (auto mod : design->modules())
			for (auto cell : mod->cells()) {
				RTLIL::Module *cell_mod = design->module(cell->type);
				if (cell_mod == nullptr)
					continue;
				for (auto &conn : cell->connections())
					if (conn.first[0] == '$' && '0' <= conn.first[1] && conn.first[1] <= '9') {
						pos_mods.insert(design->module(cell->type));
						pos_work.push_back(std::pair<RTLIL::Module*,RTLIL::Cell*>(mod, cell));
						break;
					}

				pool<std::pair<IdString, IdString>> params_rename;
				for (const auto &p : cell->parameters) {
					int id;
					if (read_id_num(p.first, &id)) {
						if (id <= 0 || id > GetSize(cell_mod->avail_parameters)) {
							log("  Failed to map positional parameter %d of cell %s.%s (%s).\n",
									id, RTLIL::id2cstr(mod->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));
						} else {
							params_rename.insert(std::make_pair(p.first, cell_mod->avail_parameters[id - 1]));
						}
					}
				}
				for (const auto &p : params_rename) {
					cell->setParam(p.second, cell->getParam(p.first));
					cell->unsetParam(p.first);
				}
			}

			for (auto module : pos_mods)
			for (auto wire : module->wires()) {
				if (wire->port_id > 0)
					pos_map[std::pair<RTLIL::Module*,int>(module, wire->port_id)] = wire->name;
			}

			for (auto &work : pos_work) {
				RTLIL::Module *module = work.first;
				RTLIL::Cell *cell = work.second;
				log("Mapping positional arguments of cell %s.%s (%s).\n",
						RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));
				dict<RTLIL::IdString, RTLIL::SigSpec> new_connections;
				for (auto &conn : cell->connections()) {
					int id;
					if (read_id_num(conn.first, &id)) {
						std::pair<RTLIL::Module*,int> key(design->module(cell->type), id);
						if (pos_map.count(key) == 0) {
							log("  Failed to map positional argument %d of cell %s.%s (%s).\n",
									id, RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));
							new_connections[conn.first] = conn.second;
						} else
							new_connections[pos_map.at(key)] = conn.second;
					} else
						new_connections[conn.first] = conn.second;
				}
				cell->connections_ = new_connections;
			}
		}

		// Determine default values
		dict<IdString, dict<IdString, Const>> defaults_db;
		if (!nodefaults)
		{
			for (auto module : design->modules())
				for (auto wire : module->wires())
					if (wire->port_input && wire->attributes.count(ID::defaultvalue))
						defaults_db[module->name][wire->name] = wire->attributes.at(ID::defaultvalue);
		}
		// Process SV implicit wildcard port connections
		std::set<Module*> blackbox_derivatives;
		std::vector<Module*> design_modules = design->modules();

		for (auto module : design_modules)
		{
			for (auto cell : module->cells())
			{
				if (!cell->get_bool_attribute(ID::wildcard_port_conns))
					continue;
				Module *m = design->module(cell->type);

				if (m == nullptr)
					log_error("Cell %s.%s (%s) has implicit port connections but the module it instantiates is unknown.\n",
							RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));

				// Need accurate port widths for error checking; so must derive blackboxes with dynamic port widths
				if (m->get_blackbox_attribute() && !cell->parameters.empty() && m->get_bool_attribute(ID::dynports)) {
					IdString new_m_name = m->derive(design, cell->parameters, true);
					if (new_m_name.empty())
						continue;
					if (new_m_name != m->name) {
						m = design->module(new_m_name);
						blackbox_derivatives.insert(m);
					}
				}

				auto old_connections = cell->connections();
				for (auto wire : m->wires()) {
					// Find ports of the module that aren't explicitly connected
					if (!wire->port_input && !wire->port_output)
						continue;
					if (old_connections.count(wire->name))
						continue;
					// Make sure a wire of correct name exists in the parent
					Wire* parent_wire = find_implicit_port_wire(module, cell, wire->name.str());

					// Missing wires are OK when a default value is set
					if (!nodefaults && parent_wire == nullptr && defaults_db.count(cell->type) && defaults_db.at(cell->type).count(wire->name))
						continue;

					if (parent_wire == nullptr)
						log_error("No matching wire for implicit port connection `%s' of cell %s.%s (%s).\n",
								RTLIL::id2cstr(wire->name), RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));
					if (parent_wire->width != wire->width)
						log_error("Width mismatch between wire (%d bits) and port (%d bits) for implicit port connection `%s' of cell %s.%s (%s).\n",
								parent_wire->width, wire->width,
								RTLIL::id2cstr(wire->name), RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));
					cell->setPort(wire->name, parent_wire);
				}
				cell->attributes.erase(ID::wildcard_port_conns);
			}
		}

		if (!nodefaults)
		{
			for (auto module : design->modules())
				for (auto cell : module->cells())
				{
					if (defaults_db.count(cell->type) == 0)
						continue;

					if (keep_positionals) {
						bool found_positionals = false;
						for (auto &conn : cell->connections())
							if (conn.first[0] == '$' && '0' <= conn.first[1] && conn.first[1] <= '9')
								found_positionals = true;
						if (found_positionals)
							continue;
					}

					for (auto &it : defaults_db.at(cell->type))
						if (!cell->hasPort(it.first))
							cell->setPort(it.first, it.second);
				}
		}

		for (auto module : design_modules)
		{
			pool<Wire*> wand_wor_index;
			dict<Wire*, SigSpec> wand_map, wor_map;
			vector<SigSig> new_connections;

			for (auto wire : module->wires())
			{
				if (wire->get_bool_attribute(ID::wand)) {
					wand_map[wire] = SigSpec();
					wand_wor_index.insert(wire);
				}
				if (wire->get_bool_attribute(ID::wor)) {
					wor_map[wire] = SigSpec();
					wand_wor_index.insert(wire);
				}
			}

			for (auto &conn : module->connections())
			{
				SigSig new_conn;
				int cursor = 0;

				for (auto c : conn.first.chunks())
				{
					Wire *w = c.wire;
					SigSpec rhs = conn.second.extract(cursor, GetSize(c));

					if (wand_wor_index.count(w) == 0) {
						new_conn.first.append(c);
						new_conn.second.append(rhs);
					} else {
						if (wand_map.count(w)) {
							SigSpec sig = SigSpec(State::S1, GetSize(w));
							sig.replace(c.offset, rhs);
							wand_map.at(w).append(sig);
						} else {
							SigSpec sig = SigSpec(State::S0, GetSize(w));
							sig.replace(c.offset, rhs);
							wor_map.at(w).append(sig);
						}
					}
					cursor += GetSize(c);
				}
				new_connections.push_back(new_conn);
			}
			module->new_connections(new_connections);

			for (auto cell : module->cells())
			{
				if (!cell->known())
					continue;

				for (auto &conn : cell->connections())
				{
					if (!cell->output(conn.first))
						continue;

					SigSpec new_sig;
					bool update_port = false;

					for (auto c : conn.second.chunks())
					{
						Wire *w = c.wire;

						if (wand_wor_index.count(w) == 0) {
							new_sig.append(c);
							continue;
						}

						Wire *t = module->addWire(NEW_ID, GetSize(c));
						new_sig.append(t);
						update_port = true;

						if (wand_map.count(w)) {
							SigSpec sig = SigSpec(State::S1, GetSize(w));
							sig.replace(c.offset, t);
							wand_map.at(w).append(sig);
						} else {
							SigSpec sig = SigSpec(State::S0, GetSize(w));
							sig.replace(c.offset, t);
							wor_map.at(w).append(sig);
						}
					}

					if (update_port)
						cell->setPort(conn.first, new_sig);
				}
			}

			for (auto w : wand_wor_index)
			{
				bool wand = wand_map.count(w);
				SigSpec sigs = wand ? wand_map.at(w) : wor_map.at(w);

				if (GetSize(sigs) == 0)
					continue;

				if (GetSize(w) == 1) {
					if (wand)
						module->addReduceAnd(NEW_ID, sigs, w);
					else
						module->addReduceOr(NEW_ID, sigs, w);
					continue;
				}

				SigSpec s = sigs.extract(0, GetSize(w));
				for (int i = GetSize(w); i < GetSize(sigs); i += GetSize(w)) {
					if (wand)
						s = module->And(NEW_ID, s, sigs.extract(i, GetSize(w)));
					else
						s = module->Or(NEW_ID, s, sigs.extract(i, GetSize(w)));
				}
				module->connect(w, s);
			}

			for (auto cell : module->cells())
			{
				Module *m = design->module(cell->type);

				if (m == nullptr)
					continue;

				bool boxed_params = false;
				if (m->get_blackbox_attribute() && !cell->parameters.empty()) {
					if (m->get_bool_attribute(ID::dynports)) {
						IdString new_m_name = m->derive(design, cell->parameters, true);
						if (new_m_name.empty())
							continue;
						if (new_m_name != m->name) {
							m = design->module(new_m_name);
							blackbox_derivatives.insert(m);
						}
					} else {
						boxed_params = true;
					}
				}

				for (auto &conn : cell->connections())
				{
					Wire *w = m->wire(conn.first);

					if (w == nullptr || w->port_id == 0)
						continue;

					if (GetSize(conn.second) == 0)
						continue;

					SigSpec sig = conn.second;

					bool resize_widths = !keep_portwidths && GetSize(w) != GetSize(conn.second);
					if (resize_widths && verific_mod && boxed_params)
						log_debug("Ignoring width mismatch on %s.%s.%s from verific, is port width parametrizable?\n",
								log_id(module), log_id(cell), log_id(conn.first)
						);
					else if (resize_widths) {
						if (GetSize(w) < GetSize(conn.second))
						{
							int n = GetSize(conn.second) - GetSize(w);
							if (!w->port_input && w->port_output)
							{
								RTLIL::SigSpec out = sig.extract(0, GetSize(w));
								out.extend_u0(GetSize(sig), w->is_signed);
								module->connect(sig.extract(GetSize(w), n), out.extract(GetSize(w), n));
							}
							sig.remove(GetSize(w), n);
						}
						else
						{
							int n = GetSize(w) - GetSize(conn.second);
							if (w->port_input && !w->port_output)
								sig.extend_u0(GetSize(w), sig.is_wire() && sig.as_wire()->is_signed);
							else
								sig.append(module->addWire(NEW_ID, n));
						}

						if (!conn.second.is_fully_const() || !w->port_input || w->port_output)
							log_warning("Resizing cell port %s.%s.%s from %d bits to %d bits.\n", log_id(module), log_id(cell),
									log_id(conn.first), GetSize(conn.second), GetSize(sig));
						cell->setPort(conn.first, sig);
					}

					if (w->port_output && !w->port_input && sig.has_const())
						log_error("Output port %s.%s.%s (%s) is connected to constants: %s\n",
								log_id(module), log_id(cell), log_id(conn.first), log_id(cell->type), log_signal(sig));
				}
			}
		}

		for (auto module : blackbox_derivatives)
			design->remove(module);

		log_pop();
	}
} HierarchyPass;

PRIVATE_NAMESPACE_END
