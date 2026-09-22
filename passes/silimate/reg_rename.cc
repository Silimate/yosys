/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Stan Lee          <stan@silimate.com>
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

#include <algorithm>

#include "kernel/ff.h"
#include "kernel/fstdata.h"
#include "kernel/newcelltypes.h"
#include "kernel/yosys.h"
#include "passes/silimate/reg_rename.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// One dumped signal belonging to an RTL object.
struct DumpLeaf {
	std::string name; // scope-relative name as dumped, which the renamed wire takes
	std::string rel;
	int width = 0;
	int offset = 0;
};

// What reg_rename made of one Q bit, stamped on every sequential cell it visits as the
// `rtl_bind_status` attribute: one word per Q bit from Q[0], written as runs (kernel/ff.h),
// e.g. "bound*4 absent*28".
//   bound      renamed onto the signal the waveform dumped for it, or already named that
//   unstamped  no usable `rtl_bind` for the bit (none, malformed, `-`, or the wrong width)
//   absent     its RTL object is not in the waveform under the instance's scope
//   unplaced   the object is in the waveform, but not this bit of it
//   conflict   the dumped bit is already driven by another flop
//   unwired    Q is not a slice of one wire that can be renamed (a constant, a concat, an input)
// Cells outside the hierarchy under the scope carry no stamp. When a module is instantiated
// more than once, a bit is `bound` only if every instance bound it.
enum BindKind { KIND_BOUND, KIND_UNSTAMPED, KIND_ABSENT, KIND_UNPLACED, KIND_CONFLICT, KIND_UNWIRED, KIND_COUNT };
static const char *const *const kind_names = RTL_BIND_STATUS_WORDS; // indexed by BindKind
static_assert(sizeof(RTL_BIND_STATUS_WORDS) / sizeof(RTL_BIND_STATUS_WORDS[0]) == KIND_COUNT);

// One summary warning: every bit of one failure kind on one object group in one scope
struct Unbound {
	std::string scope, group;
	BindKind kind = KIND_UNPLACED;
	int bits = 0;
	std::vector<std::string> objects; // distinct objects in the group, first seen first
	pool<std::string> object_set;
	int width = 0; // of the objects, when they agree
	bool mixed_width = false;
	std::vector<std::string> cells; // distinct cells, first seen first
	pool<Cell *> cell_set;
	std::string detail; // first conflicting target, or the first width mismatch
};

// End-of-pass tally, so a partial binding is reported rather than passed off as complete
struct BindStats {
	int bound = 0;
	int no_stamp = 0;
	int no_object = 0;
	int no_bit = 0;
	int bits[KIND_COUNT] = {};
	pool<Cell *> stamped; // cells given a status by this run, merged across instances
	dict<std::string, int> summary_index;
	std::vector<Unbound> summaries;
};

// Object with its trailing element indices dropped, so a whole array reports as one group
static std::string element_group(const std::string &obj)
{
	std::string group = obj;
	while (!group.empty() && group.back() == ']') {
		size_t open = group.rfind('[');
		if (open == std::string::npos || open == 0 ||
				group.find_first_not_of("0123456789", open + 1) != group.size() - 1)
			break;
		group.resize(open);
	}
	return group;
}

// `name [msb:lsb]` for a dumped signal
static std::string leaf_label(const DumpLeaf &leaf)
{
	if (leaf.width == 1 && leaf.offset == 0)
		return leaf.name;
	return stringf("%s [%d:%d]", leaf.name.c_str(), leaf.offset + leaf.width - 1, leaf.offset);
}

// Name order with embedded numbers compared by value, so x[2] comes before x[10]
static bool natural_less(const std::string &a, const std::string &b)
{
	size_t i = 0, j = 0;
	while (i < a.size() && j < b.size()) {
		if (isdigit((unsigned char)a[i]) && isdigit((unsigned char)b[j])) {
			size_t ie = std::min(a.find_first_not_of("0123456789", i), a.size());
			size_t je = std::min(b.find_first_not_of("0123456789", j), b.size());
			std::string na = a.substr(i, ie - i), nb = b.substr(j, je - j);
			na.erase(0, std::min(na.find_first_not_of('0'), na.size() - 1));
			nb.erase(0, std::min(nb.find_first_not_of('0'), nb.size() - 1));
			if (na.size() != nb.size() || na != nb)
				return na.size() != nb.size() ? na.size() < nb.size() : na < nb;
			i = ie, j = je;
			continue;
		}
		if (a[i] != b[j])
			return a[i] < b[j];
		i++, j++;
	}
	return a.size() - i < b.size() - j;
}

// Up to `cap` entries of `items` in name order, comma separated, with how many were left out
static std::string capped_list(std::vector<std::string> items, int cap)
{
	std::sort(items.begin(), items.end(), natural_less);
	std::string out;
	for (int i = 0; i < GetSize(items) && i < cap; i++)
		out += (i ? ", " : "") + items[i];
	if (GetSize(items) > cap)
		out += stringf(", ... (%d more)", GetSize(items) - cap);
	return out;
}

// Read one of the stamped integer fields.
static bool stamped_int(Cell *cell, IdString attr, int &out)
{
	if (!cell->has_attribute(attr))
		return false;
	const std::string text = cell->get_string_attribute(attr);
	if (text.empty() || text.find_first_not_of("0123456789") != std::string::npos)
		return false;
	out = std::stoi(text);
	return true;
}

// The `rtl_obj` stamp of RTLIL cached before the importer stamped `rtl_bind`
static RtlBindBit legacy_bind(Cell *cell)
{
	RtlBindBit bind;
	bind.obj = cell->get_string_attribute(ID(rtl_obj));
	bind.valid = !bind.obj.empty() && stamped_int(cell, ID(rtl_obj_bit), bind.bit) &&
			stamped_int(cell, ID(rtl_obj_width), bind.width);
	return bind;
}

static bool binds_any_bit(const std::vector<RtlBindBit> &bind)
{
	return std::any_of(bind.begin(), bind.end(), [](const RtlBindBit &b) { return b.valid; });
}

static std::string first_component(const std::string &rel)
{
	if (rel.empty())
		return rel;
	size_t end = rel.find_first_of(".[", 1);
	return end == std::string::npos ? rel : rel.substr(0, end);
}

// Group leaves by their next path component, preserving declaration order.
static std::vector<std::vector<DumpLeaf>> group_children(const std::vector<DumpLeaf> &leaves)
{
	// Key lookups to avoid quadratic runtime
	dict<std::string, int> order;
	std::vector<std::vector<DumpLeaf>> groups;
	for (auto &leaf : leaves) {
		std::string head = first_component(leaf.rel);
		auto it = order.find(head);
		if (it == order.end()) {
			it = order.insert(std::make_pair(head, GetSize(groups))).first;
			groups.push_back({});
		}
		DumpLeaf child = leaf;
		child.rel = leaf.rel.substr(head.size()); // descend one level
		groups[it->second].push_back(child);
	}
	return groups;
}

// Total width of a subtree, i.e. what it spans if its members partition the parent
static int span(const std::vector<DumpLeaf> &leaves)
{
	int total = 0;
	for (auto &leaf : leaves)
		total += leaf.width;
	return total;
}

// Locate `bit` of an object that the waveform dumped as `leaves`, given the width the
// netlist says the object has.
static bool resolve(const std::vector<DumpLeaf> &leaves, int width, int bit, DumpLeaf &out,
		    int &leaf_bit)
{
	if (leaves.empty() || bit < 0 || bit >= width)
		return false;

	// A single leaf covering the object: the bit indexes straight into it. A dump narrower
	// than the object is normal -- a converter can dump fewer bits than the register holds --
	// so place the bits it carries and leave the rest unplaced. A wider dump means the leaf
	// is not this object after all.
	if (leaves.size() == 1 && leaves[0].rel.empty()) {
		if (leaves[0].width > width || bit >= leaves[0].width)
			return false;
		out = leaves[0];
		leaf_bit = bit;
		return true;
	}

	// Several signals all named for the object itself is an ambiguous dump rather than a
	// member list, and would leave the recursion below with nothing to descend into.
	bool flat = true;
	for (auto &leaf : leaves)
		flat = flat && leaf.rel.empty();
	if (flat)
		return false;

	auto groups = group_children(leaves);
	int total = 0;
	for (auto &group : groups)
		total += span(group);

	// Struct or array: members partition the object, first declared taking the top bits
	if (total == width) {
		int high = width;
		for (auto &group : groups) {
			high -= span(group);
			if (bit >= high)
				return resolve(group, span(group), bit - high, out, leaf_bit);
		}
		return false;
	}

	// Union: every member spans the whole object, so read whichever is a plain signal
	bool overlay = !groups.empty();
	for (auto &group : groups)
		overlay = overlay && span(group) == width;
	if (overlay) {
		for (auto &group : groups)
			if (group.size() == 1 && group[0].rel.empty())
				return resolve(group, width, bit, out, leaf_bit);
		return resolve(groups.front(), width, bit, out, leaf_bit);
	}

	return false;
}

// First component of a netlist name, i.e. the RTL object before `.` or `[`
static std::string object_root(const std::string &name)
{
	size_t cut = name.find_first_of(".[");
	return cut == std::string::npos ? name : name.substr(0, cut);
}

// Parse a signed decimal, rejecting anything else. Fixed-point RTL declares vectors down
// past zero, as in `logic [19:-1] ripple_counter`, so a declared bound carries a sign.
static bool parse_bound(const std::string &text, int &out)
{
	size_t start = !text.empty() && text[0] == '-' ? 1 : 0;
	if (text.size() == start || text.find_first_not_of("0123456789", start) != std::string::npos)
		return false;
	out = std::stoi(text);
	return true;
}

// Strip a trailing bit range and report the declared lsb. A range written with no space
// before it is a packed dimension (SHM's "deep_out[1:0]"), not a bit range, but either way
// the dumped width is authoritative and the name without it is the signal.
static std::string split_bit_range(const std::string &name, int &offset)
{
	offset = 0;
	if (name.empty() || name.back() != ']')
		return name;
	size_t open = name.rfind('[');
	if (open == std::string::npos)
		return name;
	std::string inner = name.substr(open + 1, name.size() - open - 2);
	size_t colon = inner.find(':');
	if (colon == std::string::npos) // a single index is part of the name, not a range
		return name;
	int msb = 0, lsb = 0;
	if (inner.find(':', colon + 1) != std::string::npos ||
			!parse_bound(inner.substr(0, colon), msb) ||
			!parse_bound(inner.substr(colon + 1), lsb))
		return name;
	offset = std::min(msb, lsb);
	return name.substr(0, open);
}

struct RegRenameInstance {
	std::string vcd_scope;
	Module *module;
	bool debug;
	dict<Cell*, RegRenameInstance *> children;

	// Constructor
	// When constructing, it will recursively build the
	// module hierarchy with correct VCD scope mapping
	RegRenameInstance(std::string scope, Module *mod, bool dbg = false)
		: vcd_scope(scope), module(mod), debug(dbg)
	{
		// Loop through all cells in the module
		for (auto cell : module->cells()) {
			Module *child = module->design->module(cell->type);
			if (child == nullptr) {
				continue; // skip non-module cells
			}
			// Construct the child's scope in VCD format,
			// which is the parent scope plus the instance name
			std::string child_scope = vcd_scope + "." + RTLIL::unescape_id(cell->name);
			children[cell] = new RegRenameInstance(child_scope, child, debug);
		}
	}

	// Destructor
	~RegRenameInstance()
	{
		for (auto &it : children)
			delete it.second;
	}

	// Every module scope in the hierarchy, used to tell instance path from object path
	void collect_scopes(pool<std::string> &scopes)
	{
		scopes.insert(vcd_scope);
		for (auto &it : children)
			it.second->collect_scopes(scopes);
	}

	// The wire the dump expects, created at the dumped width when synthesis split the object.
	Wire *dump_wire(dict<IdString, Wire *> &cache, const DumpLeaf &leaf, const std::string &dump_path)
	{
		IdString id = RTLIL::escape_id(leaf.name);
		Wire *&wire = cache[id];
		if (!wire) {
			wire = module->wire(id);
			if (!wire) {
				if (debug)
					log("Creating wire %s[%d:%d] in scope %s\n", leaf.name.c_str(),
							leaf.offset + leaf.width - 1, leaf.offset, vcd_scope.c_str());
				wire = module->addWire(id, leaf.width);
				wire->start_offset = leaf.offset;
			}
		}
		// Dump lives in another scope, which sim will resolve through sim_src attribute
		if (!dump_path.empty())
			wire->set_string_attribute(ID(sim_src), dump_path);
		return wire;
	}

	// Move every flop collected above onto its renamed wire in one pass over the module
	void commit(const dict<SigBit, SigBit> &bit_map, const pool<SigBit> &claimed,
		    const std::vector<std::pair<SigBit, SigBit>> &aliases, const pool<Wire *> &drop)
	{
		auto rewriter = [&](SigSpec &sig) {
			for (int i = 0; i < GetSize(sig); i++) {
				auto it = bit_map.find(sig[i]);
				if (it != bit_map.end())
					sig.replace(i, SigSpec(it->second));
			}
		};
		if (!bit_map.empty())
			module->rewrite_sigspecs(rewriter);
		module->remove(drop);

		// Alias/opt left assigns (often to X) on bits the flops now own; rebuild the
		// connection list without them, keeping any unclaimed slice of each assign.
		if (!claimed.empty()) {
			std::vector<RTLIL::SigSig> kept;
			bool changed = false;
			for (auto &conn : module->connections()) {
				RTLIL::SigSpec lhs, rhs; // lhs = driven, rhs = driver
				for (int i = 0; i < GetSize(conn.first); i++) {
					if (claimed.count(conn.first[i])) {
						changed = true;
						continue;
					}
					lhs.append(conn.first[i]);
					rhs.append(conn.second[i]);
				}
				if (GetSize(lhs))
					kept.emplace_back(lhs, rhs);
			}
			if (changed)
				module->new_connections(kept);
		}

		// Added last: the rewrite above would otherwise turn these into self-assigns.
		for (auto &alias : aliases)
			module->connect(alias.first, alias.second);
	}

	// Record what became of `count` Q bits of `cell` from Q bit `q`, and fold a failure into the
	// summary warning for its object
	void note(BindStats &stats, std::vector<int> &status, Cell *cell, int q, int count, BindKind kind,
		  const std::string &obj = "", int obj_width = 0, const std::string &detail = "")
	{
		for (int i = 0; i < count; i++)
			status[q + i] = kind;
		stats.bits[kind] += count;
		if (kind == KIND_BOUND)
			return;

		std::string group = element_group(obj);
		std::string key = stringf("%d\n%s\n%s", kind, vcd_scope.c_str(), group.c_str());
		auto it = stats.summary_index.find(key);
		if (it == stats.summary_index.end()) {
			it = stats.summary_index.insert(std::make_pair(key, GetSize(stats.summaries))).first;
			stats.summaries.emplace_back();
			Unbound &u = stats.summaries.back();
			u.scope = vcd_scope;
			u.group = group;
			u.kind = kind;
			u.width = obj_width;
			u.detail = detail;
		}
		Unbound &u = stats.summaries[it->second];
		u.bits += count;
		u.mixed_width |= obj_width != u.width;
		if (!obj.empty() && u.object_set.insert(obj).second)
			u.objects.push_back(obj);
		if (u.cell_set.insert(cell).second && GetSize(u.cells) < 8)
			u.cells.push_back(log_id(cell->name));
	}

	// Stamp `rtl_bind_status`. Another instance of this module may have stamped the cell earlier
	// in this run; a bit stays `bound` only if both bound it.
	void stamp_status(BindStats &stats, Cell *cell, const std::vector<int> &status)
	{
		std::vector<std::string> words;
		for (int s : status)
			words.push_back(kind_names[s]);
		if (!stats.stamped.insert(cell).second) {
			std::vector<std::string> prev = rtl_bind_status_expand(cell->get_string_attribute(ID(rtl_bind_status)));
			if (GetSize(prev) == GetSize(words))
				for (int i = 0; i < GetSize(words); i++)
					if (prev[i] != kind_names[KIND_BOUND])
						words[i] = prev[i];
		}
		cell->set_string_attribute(ID(rtl_bind_status), rtl_bind_status_compress(words));
	}

	// Stamp a bind verdict on each inferred clock gate, from its enable.
	//
	// An ICG has no RTL object of its own to decode: it is synthesised from the gating logic,
	// and its GCLK output is computed by resim rather than dumped, so no waveform can carry it.
	// Its enable decides the verdict, and the question there is whether the enable is
	// determined, not whether it was dumped under a name -- gating logic is internal, so an
	// enable is rarely a dumped signal and would otherwise read as absent almost everywhere.
	//
	// So an enable counts when the waveform holds it, when a constant fixes it, or when logic
	// inside this module drives it, since resim then computes it from a fanin the registers
	// above have already bound. It is absent only when nothing determines it: an input port
	// that no lookup resolved. Runs after process_registers so those Q wires already carry
	// their dumped names.
	void stamp_icgs(const dict<std::string, std::vector<DumpLeaf>> &objects, BindStats &stats)
	{
		pool<SigBit> driven; // filled on the first ICG, since most modules have none
		bool have_driven = false;

		for (auto cell : module->cells()) {
			if (cell->type != ID($icg) || !cell->hasPort(ID::EN))
				continue;
			SigSpec en = cell->getPort(ID::EN);
			std::vector<int> status(1, KIND_UNWIRED);
			if (GetSize(en) != 1) {
				note(stats, status, cell, 0, 1, KIND_UNWIRED);
				stamp_status(stats, cell, status);
				continue;
			}
			if (!have_driven) {
				for (auto other : module->cells())
					for (auto &conn : other->connections())
						if (other->output(conn.first))
							for (auto bit : conn.second)
								driven.insert(bit);
				for (auto &conn : module->connections())
					for (auto bit : conn.first)
						driven.insert(bit);
				have_driven = true;
			}

			SigBit bit = en[0];
			std::string name = bit.is_wire() ? RTLIL::unescape_id(bit.wire->name) : "";
			bool bound = !bit.is_wire() || driven.count(bit) ||
					bit.wire->has_attribute(ID(sim_src)) ||
					bit.wire->has_attribute(ID(sim_const)) ||
					objects.count(vcd_scope + "." + object_root(name));
			note(stats, status, cell, 0, 1, bound ? KIND_BOUND : KIND_ABSENT,
					bound ? "" : name, 1);
			stamp_status(stats, cell, status);
			if (debug)
				log("ICG %s.%s enable %s: %s\n", vcd_scope.c_str(), log_id(cell->name),
						name.c_str(), bound ? "bound" : "absent");
		}
	}

	// Rename each flop's Q wire to the signal the waveform dumped it under.
	void process_registers(const dict<std::string, std::vector<DumpLeaf>> &objects,
			       BindStats &stats)
	{
		if (debug)
			log("Processing registers in scope: %s (module: %s)\n", vcd_scope.c_str(),
					log_id(module->name));
		else
			log("Processing registers in %s\n", log_id(module->name));

		dict<SigBit, SigBit> bit_map; // old flop bit -> bit of the renamed wire
		pool<SigBit> claimed_bits;
		std::vector<std::pair<SigBit, SigBit>> port_aliases; // output bits to re-drive
		dict<IdString, Wire *> target_wires;
		pool<Wire *> drop_wires;

		for (auto cell : module->cells()) {
			if (!StaticCellTypes::categories.is_ff(cell->type) || !cell->hasPort(ID::Q))
				continue;
			SigSpec q = cell->getPort(ID::Q);
			std::vector<int> status(GetSize(q), KIND_UNWIRED);
			if (status.empty())
				continue;

			// Which RTL object bits this flop holds, stamped by the importer (kernel/ff.h)
			std::vector<RtlBindBit> bind = rtl_bind_expand(cell->get_string_attribute(ID(rtl_bind)));
			if (!binds_any_bit(bind))
				bind = {legacy_bind(cell)};
			if (!binds_any_bit(bind)) {
				if (debug)
					log("Cell %s in scope %s has no usable RTL bind stamp\n",
							log_id(cell->name), vcd_scope.c_str());
				note(stats, status, cell, 0, GetSize(q), KIND_UNSTAMPED);
				stats.no_stamp++;
				stamp_status(stats, cell, status);
				continue;
			}

			// A field of a split struct port drives a slice of a wider wire, so take the
			// flop's own bits rather than assuming it owns all of old_wire.
			if (!q.is_chunk() || !q.as_chunk().wire || q.as_chunk().wire->port_input) {
				if (debug)
					log("Cell %s in scope %s drives no wire that can be renamed (%s)\n",
							log_id(cell->name), vcd_scope.c_str(), log_signal(q));
				note(stats, status, cell, 0, GetSize(q), KIND_UNWIRED);
				stamp_status(stats, cell, status);
				continue;
			}
			SigChunk qbits = q.as_chunk();
			Wire *old_wire = qbits.wire;

			// A legacy stamp names the first bit only; the rest of the cell follows it
			if (GetSize(bind) == 1)
				for (int i = 1; i < qbits.width; i++) {
					bind.push_back(bind[0]);
					bind.back().bit += i;
				}
			if (GetSize(bind) != qbits.width) {
				std::string detail = stringf("%s has a %d-bit RTL bind stamp for %d Q bit(s)",
						log_id(cell->name), GetSize(bind), qbits.width);
				if (debug)
					log("Cell %s in scope %s\n", detail.c_str(), vcd_scope.c_str());
				note(stats, status, cell, 0, qbits.width, KIND_UNSTAMPED, "", 0, detail);
				stats.no_stamp++;
				stamp_status(stats, cell, status);
				continue;
			}

			// Rename each run of Q bits bound to consecutive bits of one object, within one dumped signal
			int bound_bits = 0, renamed_bits = 0;
			for (int start = 0, end; start < qbits.width; start = end) {
				for (end = start + 1; end < qbits.width && bind[end].valid && bind[end].obj == bind[start].obj &&
						bind[end].width == bind[start].width && bind[end].bit == bind[end - 1].bit + 1; end++);
				if (!bind[start].valid) {
					if (debug)
						log("Q bit %d of cell %s in scope %s has no RTL bind\n",
								start, log_id(cell->name), vcd_scope.c_str());
					note(stats, status, cell, start, 1, KIND_UNSTAMPED);
					stats.no_stamp++;
					continue;
				}
				std::string obj = bind[start].obj;
				int obj_bit = bind[start].bit, obj_width = bind[start].width;

				// Locate obj[obj_bit] among the signals the waveform dumped for it
				auto obj_it = objects.find(vcd_scope + "." + obj);
				DumpLeaf leaf;
				int leaf_bit = 0;
				std::string dump_path;
				bool placed = obj_it != objects.end() &&
						resolve(obj_it->second, obj_width, obj_bit, leaf, leaf_bit);

				// A flattened interface pin is dumped under the parent's actual, so it is not
				// in this scope's object map. bind_input_ports already put that path on the
				// pin, so rename onto the pin itself and let sim_src do the lookup.
				Wire *pin = placed ? nullptr : module->wire(RTLIL::escape_id(obj));
				if (pin && pin->has_attribute(ID(sim_src)) && GetSize(pin) == obj_width &&
						obj_bit >= 0 && obj_bit < obj_width) {
					dump_path = pin->get_string_attribute(ID(sim_src));
					leaf = {obj, "", GetSize(pin), pin->start_offset};
					leaf_bit = obj_bit;
					placed = true;
				}

				// The stamp may name an object the dump does not hold as such: a layout rebuilt
				// from wire names takes the generate block of `hw_gen.cnt` for a struct. Q still
				// drives that net, so bind through the net's own name when the dump has it.
				if (!placed && old_wire->name.isPublic()) {
					auto net_it = objects.find(vcd_scope + "." + RTLIL::unescape_id(old_wire->name));
					placed = net_it != objects.end() &&
							resolve(net_it->second, GetSize(old_wire), qbits.offset + start, leaf, leaf_bit);
					if (placed && debug)
						log("Placing %s[%d] of cell %s by its Q net as %s, not by its RTL bind %s[%d]\n",
								log_id(old_wire), qbits.offset + start, log_id(cell->name),
								leaf.name.c_str(), obj.c_str(), obj_bit);
				}

				if (!placed) {
					bool absent = obj_it == objects.end();
					if (debug)
						log("%s bit %d of %d-bit object %s, dumped as %d signal(s), for cell %s in scope %s\n",
								absent ? "No waveform object for" : "Cannot place", obj_bit, obj_width,
								obj.c_str(), absent ? 0 : GetSize(obj_it->second), log_id(cell->name),
								vcd_scope.c_str());
					note(stats, status, cell, start, end - start, absent ? KIND_ABSENT : KIND_UNPLACED,
							obj, obj_width);
					(absent ? stats.no_object : stats.no_bit)++;
					continue;
				}

				// A multi-bit flop can straddle dumped signals, e.g. two struct members: bind the
				// part inside this one and place the rest from where it ends
				if (leaf_bit < 0 || leaf_bit >= leaf.width) {
					if (debug)
						log("Bit index %d is invalid for wire indices [%d:%d] for '%s'\n",
								leaf.offset + leaf_bit, leaf.offset + leaf.width - 1, leaf.offset,
								leaf.name.c_str());
					note(stats, status, cell, start, end - start, KIND_UNPLACED, obj, obj_width);
					stats.no_bit++;
					continue;
				}
				end = std::min(end, start + leaf.width - leaf_bit);
				SigChunk run(old_wire, qbits.offset + start, end - start);

				Wire *target = dump_wire(target_wires, leaf, dump_path);
				if (target == old_wire) {
					// Already the wire the dump expects, as long as the bits line up
					bool aligned = leaf_bit == run.offset;
					if (debug)
						log("%s %s (%s[%d]) %s %s[%d]\n", aligned ? "Keeping" : "Cannot move",
								log_id(old_wire), obj.c_str(), obj_bit, aligned ? "as" : "within",
								leaf.name.c_str(), leaf.offset + leaf_bit);
					if (aligned)
						bound_bits += run.width;
					note(stats, status, cell, start, run.width, aligned ? KIND_BOUND : KIND_CONFLICT, obj,
							obj_width, stringf("%s[%d]", leaf.name.c_str(), leaf.offset + leaf_bit));
					continue;
				}

				// Multiple-driver guard: another flop may have claimed these bits, or the
				// netlist already holds a narrower wire under the dumped name
				bool taken = leaf_bit + run.width > GetSize(target);
				for (int i = 0; i < run.width && !taken; i++)
					taken = claimed_bits.count(SigBit(target, leaf_bit + i));
				if (taken) {
					if (debug)
						log("Skipping cell %s: target %s[%d] already driven by another cell\n",
								log_id(cell->name), leaf.name.c_str(), leaf.offset + leaf_bit);
					note(stats, status, cell, start, run.width, KIND_CONFLICT, obj, obj_width,
							stringf("%s[%d]", leaf.name.c_str(), leaf.offset + leaf_bit));
					continue;
				}

				if (debug)
					log("Connecting %s (%s[%d]) to %s[%d]\n", log_id(old_wire), obj.c_str(),
							obj_bit, leaf.name.c_str(), leaf.offset + leaf_bit);

				note(stats, status, cell, start, run.width, KIND_BOUND);
				bound_bits += run.width;
				renamed_bits += run.width;
				for (int i = 0; i < run.width; i++) {
					SigBit old(old_wire, run.offset + i);
					SigBit renamed(target, leaf_bit + i);
					bit_map[old] = renamed;
					claimed_bits.insert(renamed);
					// Moving the flop off an output port leaves it undriven; alias it back.
					if (old_wire->port_output)
						port_aliases.emplace_back(old, renamed);
				}
			}
			stamp_status(stats, cell, status);
			if (bound_bits)
				stats.bound++;
			// Drop the old wire only when the flop drove all of it and nothing else can.
			if (renamed_bits && renamed_bits == GetSize(old_wire) && !old_wire->port_id)
				drop_wires.insert(old_wire);
		}

		commit(bit_map, claimed_bits, port_aliases, drop_wires);
	}

	// Resolve each child's input ports through the parent's actual, for the ports a dump does
	// not carry under the child's own scope: an interface modport member, a struct field, and
	// an unpacked-array element are all split into one port per leaf, while the waveform holds
	// only the parent signal those ports are wired to.
	void bind_input_ports(FstData &fst)
	{
		for (auto &it : children) {
			Cell *cell = it.first;
			RegRenameInstance *child = it.second;
			for (auto wire : child->module->wires()) {
				if (!wire->port_input || wire->port_output || !cell->hasPort(wire->name))
					continue;
				// The dump carries this port under the child's own scope, which sim looks up
				// first; resolving it through the parent as well would say nothing new.
				fstHandle own = fst.getHandle(child->vcd_scope + "." +
						RTLIL::unescape_id(wire->name));
				if (own && (int)fst.getWidth(own) == GetSize(wire))
					continue;
				SigSpec sig = cell->getPort(wire->name);
				// Parent ties the pin off; the cut removes that driver, so carry the value.
				if (sig.is_fully_const()) {
					wire->set_string_attribute(ID(sim_const), sig.as_const().as_string());
					continue;
				}
				if (!sig.is_chunk())
					continue; // a concat spans more than one dumped signal
				SigChunk chunk = sig.as_chunk();
				Wire *actual = chunk.wire;
				if (!actual)
					continue;
				int offset = chunk.offset;

				// A passthrough pin's parent may itself be tied off, which only the level
				// above could see, so carry that value one more hop.
				if (actual->has_attribute(ID(sim_const))) {
					wire->set_string_attribute(ID(sim_const),
							actual->get_string_attribute(ID(sim_const)));
					continue;
				}
				std::string src;
				if (actual->has_attribute(ID(sim_src))) {
					src = actual->get_string_attribute(ID(sim_src));
					// The level above resolved its own port to a slice; ours sits inside it.
					if (actual->has_attribute(ID(sim_src_bit)))
						offset += std::stoi(actual->get_string_attribute(ID(sim_src_bit)));
				} else {
					src = vcd_scope + "." + RTLIL::unescape_id(actual->name);
				}
				fstHandle id = fst.getHandle(src);
				if (!id || offset < 0 || offset + GetSize(wire) > (int)fst.getWidth(id))
					continue;
				wire->set_string_attribute(ID(sim_src), src);
				if (offset || (int)fst.getWidth(id) != GetSize(wire))
					wire->set_string_attribute(ID(sim_src_bit), std::to_string(offset));
				if (debug)
					log("Input port %s.%s resolved to %s[%d]\n", child->vcd_scope.c_str(),
							RTLIL::unescape_id(wire->name).c_str(), src.c_str(), offset);
			}
			child->bind_input_ports(fst);
		}
	}

	// Handle packed inputs.
	void bind_packed_inputs(const dict<std::string, std::vector<DumpLeaf>> &objects, FstData &fst)
	{
		// Split input ports whose dump is one packed vector
		dict<std::string, std::vector<std::tuple<int, int, Wire*>>> groups;
		int order = 0;
		for (auto wire : module->wires()) {
			if (!wire->port_input || wire->get_bool_attribute(ID(interface_port)))
				continue;
			std::string name = RTLIL::unescape_id(wire->name);
			std::string root = object_root(name);
			if (root == name)
				continue; // dumped under the same name as the port
			groups[root].emplace_back(wire->port_id ? wire->port_id : (1 << 30), order++, wire);
		}
		for (auto &kv : groups) {
			auto members = kv.second;
			std::sort(members.begin(), members.end());
			int total = 0;
			for (auto &m : members)
				total += GetSize(std::get<2>(m));
			auto obj_it = objects.find(vcd_scope + "." + kv.first);
			if (obj_it == objects.end())
				continue;
			int high = total;
			for (auto &m : members) {
				Wire *wire = std::get<2>(m);
				high -= GetSize(wire);
				DumpLeaf leaf;
				int leaf_bit = 0;
				if (!resolve(obj_it->second, total, high, leaf, leaf_bit))
					continue;
				std::string dump_path = leaf.name;
				if (dump_path.compare(0, vcd_scope.size(), vcd_scope) != 0)
					dump_path = vcd_scope + "." + dump_path;
				if (!fst.getHandle(dump_path))
					continue;
				wire->set_string_attribute(ID(sim_src), dump_path);
				if (leaf.width != GetSize(wire))
					wire->set_string_attribute(ID(sim_src_bit), std::to_string(leaf_bit));
				if (debug)
					log("Packed input %s.%s resolved to %s[%d]\n", vcd_scope.c_str(),
							log_id(wire), dump_path.c_str(), leaf_bit);
			}
		}
	}

	void process_all(const dict<std::string, std::vector<DumpLeaf>> &objects,
			 BindStats &stats, FstData &fst)
	{
		bind_packed_inputs(objects, fst);
		process_registers(objects, stats);
		stamp_icgs(objects, stats);
		for (auto &it : children)
			it.second->process_all(objects, stats, fst);
	}
};

// Group every dumped signal under the RTL object it belongs to.
static dict<std::string, std::vector<DumpLeaf>> collect_objects(FstData &fst,
								const pool<std::string> &scopes,
								bool debug)
{
	dict<std::string, std::vector<DumpLeaf>> objects;
	pool<std::string> seen; // dumpers may open the same scope twice and repeat declarations
	for (auto &var : fst.getVars()) {
		int offset = 0;
		std::string name = split_bit_range(RTLIL::unescape_id(var.name), offset);
		std::string full = var.scope.empty() ? name : var.scope + "." + name;

		// Longest enclosing module scope: the rest is the object and its member path
		std::string scope = var.scope;
		while (!scope.empty() && !scopes.count(scope)) {
			size_t dot = scope.find_last_of('.');
			scope = dot == std::string::npos ? "" : scope.substr(0, dot);
		}
		if (scope.empty() && !scopes.count(scope))
			continue; // outside the hierarchy being processed

		std::string rel = full.substr(scope.empty() ? 0 : scope.size() + 1);

		// A repeat of a name already seen is the same signal again, not another member
		if (!seen.insert(full).second)
			continue;

		DumpLeaf leaf;
		leaf.name = rel;
		// An array dumped as a scope holding its elements (`$scope data_pipes_reg` over
		// `$var [1]`) files element `data_pipes_reg[1]` under that object, while the renamed
		// wire keeps the dumped spelling `data_pipes_reg.[1]`, which sim finds from any
		// instance's own scope.
		for (size_t pos; (pos = rel.find(".[")) != std::string::npos;)
			rel.erase(pos, 1);
		leaf.width = var.width;
		leaf.offset = offset;
		if (debug)
			log("Dumped %s.%s (width %d, lsb %d)\n", scope.c_str(), rel.c_str(), leaf.width, offset);
		for (size_t split = rel.find_first_of(".[");; split = rel.find_first_of(".[", split + 1)) {
			leaf.rel = split == std::string::npos ? "" : rel.substr(split);
			objects[scope + "." + rel.substr(0, split)].push_back(leaf);
			if (split == std::string::npos)
				break;
		}
	}
	return objects;
}

// `N signal(s) spanning B bit(s): a [3:0], b`, listing at most 8 of them
static std::string describe_dump(const std::vector<DumpLeaf> &leaves)
{
	std::vector<std::string> labels;
	for (auto &leaf : leaves)
		labels.push_back(leaf_label(leaf));
	return stringf("%d signal(s) spanning %d bit(s): %s", GetSize(leaves), span(leaves),
			capped_list(labels, 8).c_str());
}

// What the waveform holds for the nearest enclosing object of `obj` that it dumped at all
static std::string dumped_context(const dict<std::string, std::vector<DumpLeaf>> &objects,
				  const std::string &scope, const std::string &obj)
{
	std::string prefix = obj;
	for (size_t cut; (cut = prefix.find_last_of(".[")) != std::string::npos && cut > 0;) {
		prefix.resize(cut);
		auto it = objects.find(scope + "." + prefix);
		if (it != objects.end())
			return stringf("the waveform has %s only as %s", prefix.c_str(), describe_dump(it->second).c_str());
	}
	return stringf("nothing named %s is dumped in that scope", prefix.c_str());
}

// One warning per object group left (partly) unbound, capped so a design-wide miss stays readable
static void report_unbound(const BindStats &stats, const dict<std::string, std::vector<DumpLeaf>> &objects,
			   bool debug)
{
	const int max_warnings = 100;
	int shown = 0, hidden = 0, hidden_bits = 0;
	for (auto &u : stats.summaries) {
		std::vector<std::string> examples = u.cells;
		std::sort(examples.begin(), examples.end(), natural_less);
		examples.resize(std::min(3, GetSize(examples)));
		std::string cells = stringf("%d cell(s), e.g. %s", GetSize(u.cell_set), capped_list(examples, 3).c_str());
		if (u.kind == KIND_UNWIRED) { // never bindable, and not a waveform problem
			log("In scope %s, %d Q bit(s) of %s, drive no wire reg_rename can rename\n", u.scope.c_str(),
					u.bits, cells.c_str());
			continue;
		}
		if (!debug && shown >= max_warnings) {
			hidden++;
			hidden_bits += u.bits;
			continue;
		}
		shown++;

		std::vector<std::string> objs = u.objects;
		std::sort(objs.begin(), objs.end(), natural_less);
		std::string first = objs.empty() ? "" : objs[0];

		// `8-bit object x`, or `3 objects x[1], x[2], x[3] of 4 bits each` for elements of one array
		std::string what = GetSize(u.objects) == 1
			? stringf("%d-bit object %s", u.width, first.c_str())
			: stringf("%d objects %s%s", GetSize(u.objects), capped_list(u.objects, 4).c_str(),
					u.mixed_width ? "" : stringf(" of %d bits each", u.width).c_str());
		switch (u.kind) {
		case KIND_UNSTAMPED:
			log_warning("In scope %s, %d Q bit(s) of %s, have no usable RTL bind stamp%s%s\n", u.scope.c_str(),
					u.bits, cells.c_str(), u.detail.empty() ? "" : "; ", u.detail.c_str());
			break;
		case KIND_ABSENT:
			log_warning("Cannot place %d bit(s) of %s, %s, in scope %s: not in the waveform; %s\n", u.bits,
					what.c_str(), cells.c_str(), u.scope.c_str(),
					dumped_context(objects, u.scope, first).c_str());
			break;
		case KIND_UNPLACED: {
			auto it = objects.find(u.scope + "." + first);
			log_warning("Cannot place %d bit(s) of %s, %s, in scope %s: the waveform has %s as %s\n", u.bits,
					what.c_str(), cells.c_str(), u.scope.c_str(), first.c_str(),
					it == objects.end() ? "nothing" : describe_dump(it->second).c_str());
			break;
		}
		case KIND_CONFLICT:
			log_warning("Cannot place %d bit(s) of %s, %s, in scope %s: dumped bit %s is already driven by "
					"another cell\n", u.bits, what.c_str(), cells.c_str(), u.scope.c_str(), u.detail.c_str());
			break;
		default:
			break;
		}
	}
	if (hidden)
		log_warning("%d more object(s) left %d Q bit(s) unbound; rerun reg_rename with -d to list every one\n",
				hidden, hidden_bits);
}

struct RegRenamePass : public Pass {
	RegRenamePass()
	    : Pass("reg_rename", "renames register output wires to the correct "
				"register name and creates new wires for multi-bit registers for "
				"correct VCD register annotations.")
	{
	}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    reg_rename [options]\n");
		log("\n");
		log("    -waveform <filename>\n");
		log("        waveform file (VCD or FST) to extract original register widths from.\n");
		log("        VCD inputs are converted via the external vcd2fst tool.\n");
		log("    -scope <scope>\n");
		log("        scope to process in the waveform\n");
		log("\n");
		log("    -d\n");
		log("        enable debug output, including a line for every flop bit left unbound\n");
		log("        and every unbound-object warning (at most 100 are printed without -d)\n");
		log("\n");
		log("Every sequential cell visited gets an `rtl_bind_status` attribute with one word\n");
		log("per Q bit, from Q[0], as runs `word` or `word*count` (e.g. \"bound*4 absent*28\"):\n");
		log("bound (renamed onto its dumped signal, or already named that), unstamped (no\n");
		log("usable `rtl_bind`), absent (object not in the waveform), unplaced (object\n");
		log("dumped, bit not found in it), conflict (dumped bit already driven by another\n");
		log("flop) or unwired (Q is not a slice of one renamable wire).\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing reg_rename pass\n");

		// Argument parsing
		std::string waveform_filename;
		std::string scope;
		bool debug = false;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-waveform" && argidx + 1 < args.size()) {
				waveform_filename = args[++argidx];
				continue;
			}
			if (args[argidx] == "-scope" && argidx + 1 < args.size()) {
				scope = normalize_scope(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-d") {
				debug = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		// Extract top module
		Module *topmod = design->top_module();
		if (!topmod)
			log_error("No top module found!\n");

		if (waveform_filename.empty())
			log_error("No waveform file provided. Use -waveform option.\n");

		log("Reading waveform file: %s\n", waveform_filename.c_str());
		try {
			FstData fst(waveform_filename);
			if (scope.empty()) {
				scope = fst.autoScope(topmod);
				if (scope.empty())
					log_error("No scope found for module '%s'. Please specify -scope explicitly.\n",
						RTLIL::unescape_id(topmod->name).c_str());
			}
			log("Using scope: \"%s\"\n", scope.c_str());

			log("Building hierarchy from scope: %s\n", scope.c_str());
			RegRenameInstance root(scope, topmod, debug);

			// Module scopes first, so a dumped name can be split into instance path and object
			pool<std::string> scopes;
			root.collect_scopes(scopes);
			auto objects = collect_objects(fst, scopes, debug);
			log("Extracted %d RTL object(s) from waveform\n", GetSize(objects));

			root.bind_input_ports(fst);
			BindStats stats;
			root.process_all(objects, stats, fst);
			report_unbound(stats, objects, debug);
			log("Bound %d flop(s); unstamped %d, object absent %d, bit unplaced %d\n",
				stats.bound, stats.no_stamp, stats.no_object, stats.no_bit);
			log("Bound %d of %d Q bit(s); unstamped %d, absent %d, unplaced %d, conflict %d, unwired %d\n",
				stats.bits[KIND_BOUND], stats.bits[KIND_BOUND] + stats.bits[KIND_UNSTAMPED] +
				stats.bits[KIND_ABSENT] + stats.bits[KIND_UNPLACED] + stats.bits[KIND_CONFLICT] +
				stats.bits[KIND_UNWIRED], stats.bits[KIND_UNSTAMPED], stats.bits[KIND_ABSENT],
				stats.bits[KIND_UNPLACED], stats.bits[KIND_CONFLICT], stats.bits[KIND_UNWIRED]);
		} catch (const std::exception &e) {
			log_error("Failed to read waveform file '%s': %s\n", 
				waveform_filename.c_str(), e.what());
		}

		log_flush();
	}
} RegRenamePass;

PRIVATE_NAMESPACE_END
