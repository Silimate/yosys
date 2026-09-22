/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026 Stan Lee <stan@silimate.com>
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

#include "frontends/verific/rtl_bind.h"

#ifdef YOSYS_ENABLE_VERIFIC

#include "DataBase.h"

USING_YOSYS_NAMESPACE
using namespace Verific;

// Decimal index, optionally negative: unpacked ranges such as `mem [-2:-1]` are legal
static bool parse_int(const std::string &text, int &value)
{
	size_t start = text.size() > 1 && text[0] == '-' ? 1 : 0;
	if (text.size() == start || text.find_first_not_of("0123456789", start) != std::string::npos)
		return false;
	value = std::stoi(text);
	return true;
}

// Split ".m[3][0]" from `pos` into Step values: member "m", then indices 3 and 0
bool RtlBinder::parse_steps(const std::string &path, size_t pos, std::vector<Step> &steps) const
{
	steps.clear();
	while (pos < path.size()) {
		Step step;
		size_t end;
		if (path[pos] == '[') {
			end = path.find(']', pos);
			if (end == std::string::npos || !parse_int(path.substr(pos + 1, end - pos - 1), step.index))
				return false;
			step.is_index = true;
			end++;
		} else if (path[pos] == '.') {
			end = std::min(path.find_first_of(".[", pos + 1), path.size());
			step.member = path.substr(pos + 1, end - pos - 1);
			if (step.member.empty())
				return false;
		} else
			return false;
		steps.push_back(step);
		pos = end;
	}
	return true;
}

// Shortest prefix of `path` that Verific has a type for. "foo.a" can still root at "foo"
const TypeRange *RtlBinder::find_variable(const std::string &path, std::string &var, std::vector<Step> &steps) const
{
	const Map *table = nl->GetTypeRangeTable();
	if (path.find_first_of(" \t\r\n") != std::string::npos)
		return nullptr; // `rtl_bind` tokens are space separated, such a name cannot be carried
	for (size_t cut = 1; table && cut <= path.size(); cut++) {
		if (cut < path.size() && path[cut] != '.' && path[cut] != '[')
			continue; // only try at "foo", "foo.a", "foo[3]", not mid-identifier
		var = path.substr(0, cut);
		if (const TypeRange *tr = (const TypeRange *)table->GetValue(var.c_str()))
			return parse_steps(path, cut, steps) ? tr : nullptr;
	}
	// An interface instance is flattened into its module under `<instance>_<member>`, so a name
	// the table has no entry for can still be a member of one it does. The dump spells that
	// member `<instance>.<member>`, which is the step this rebuilds. Tried only after the scan
	// above, so a variable whose own name holds an underscore still matches whole.
	for (size_t cut = path.find('_'); table && cut != std::string::npos; cut = path.find('_', cut + 1)) {
		var = path.substr(0, cut);
		const TypeRange *tr = (const TypeRange *)table->GetValue(var.c_str());
		if (!tr)
			continue;
		std::string dotted = path;
		dotted[cut] = '.';
		if (parse_steps(dotted, cut, steps))
			return tr;
	}
	return nullptr;
}

// Packed = one waveform signal. Unpacked = each index is its own dumped object
bool RtlBinder::range_packed(const TypeRange *t) const
{
	if (!t->IsTypeArray() || t->IsPackedDimensionRange())
		return true; // struct/leaf, or SV packed array
	if (!vhdl)
		return false;
	const TypeRange *next = t->GetNext();
	// VHDL: vector of bits (array over a 1-bit leaf) dumps as one signal
	return !next || (!next->IsTypeArray() && next->NumElements() == 1);
}

// Walk the type chain and split dimensions into unpacked vs packed
bool RtlBinder::decl_shape(const TypeRange *tr, Shape &shape) const
{
	for (const TypeRange *t = tr; t; t = t->GetNext()) {
		if (!t->IsTypeArray()) {
			shape.packed_bits *= t->NumElements(); // struct/union leaf width
			break;
		}
		int msb = t->LeftRangeBound(), lsb = t->RightRangeBound();
		long long width = std::abs(msb - lsb) + 1;
		if (range_packed(t)) {
			shape.packed.emplace_back(msb, lsb);
			shape.packed_bits *= width;
		} else {
			shape.unpacked.emplace_back(msb, lsb);
			shape.elements *= width;
		}
	}
	return !tr || shape.width() == (long long)tr->NumElements();
}

// Verific-flat bit -> dump-order bit. Unpacked: Verific counts |index-lsb| from the
// bottom, innermost fastest; the dump puts the lowest index on top (MSB side)
bool RtlBinder::Shape::bit(long long flat, long long &dump) const
{
	if (flat < 0)
		return false;
	long long rest = flat / packed_bits, element = 0; // which unpacked element, Verific order
	std::vector<long long> at(unpacked.size());
	for (size_t k = unpacked.size(); k-- > 0;) { // innermost dimension first
		int msb = unpacked[k].first, lsb = unpacked[k].second;
		long long width = std::abs(msb - lsb) + 1, pos = rest % width;
		at[k] = msb >= lsb ? width - 1 - pos : pos; // flip downto ranges so low index is on top
		rest /= width;
	}
	if (rest)
		return false; // flat is past the end of this shape
	for (size_t k = 0; k < unpacked.size(); k++)
		element = element * (std::abs(unpacked[k].first - unpacked[k].second) + 1) + at[k];
	dump = element * packed_bits + flat % packed_bits; // packed bits keep Verific's LSB-first order
	return true;
}

// Q bit `b` of this location -> bit index in the whole variable
bool RtlBinder::Location::var_bit(long long b, long long &out) const
{
	long long dump;
	if (!shape.bit(b, dump))
		return false;
	out = offset + dump;
	return true;
}

// Q bit `b` -> {obj, obj_width, bit} relative to the unpacked element we anchored at
RtlBindBit RtlBinder::Location::bind(long long b) const
{
	RtlBindBit bind;
	long long v;
	if (!var_bit(b, v))
		return bind;
	bind.valid = true;
	bind.obj = obj;
	bind.width = obj_width;
	bind.bit = v - obj_offset; // 0 is the LSB of this unpacked element
	return bind;
}

// Follow the steps down the variable's type, recording every point; empty when they do not fit
std::vector<RtlBinder::WalkPoint> RtlBinder::walk(const TypeRange *head, const std::vector<Step> &steps) const
{
	std::vector<WalkPoint> points(1);
	points[0].node = head;
	points[0].span = head->NumElements();
	for (auto &step : steps) {
		WalkPoint at = points.back(), next;
		if (!at.node)
			return {};
		if (step.is_index) {
			if (at.node->IsTypeStructure())
				return {};
			int msb = at.node->LeftRangeBound(), lsb = at.node->RightRangeBound();
			int lo = std::min(msb, lsb), hi = std::max(msb, lsb);
			long long width = hi - lo + 1;
			if (step.index < lo || step.index > hi || at.span % width != 0)
				return {};
			bool packed = range_packed(at.node);
			next.node = at.node->IsTypeArray() ? at.node->GetNext() : nullptr;
			next.span = at.span / width; // bits under one index of this dimension
			// packed: |index-lsb| from the LSB. unpacked: high index first (matches dump)
			next.offset = at.offset + (packed ? std::abs(step.index - lsb) : hi - step.index) * next.span;
			next.lsb_step = step.index == lsb; // true if this index only names the LSB
			next.element = !packed;
			next.index = step.index;
		} else {
			Map *members = at.node->IsTypeStructure() ? at.node->GetElementTypeRangeMap() : nullptr;
			if (!members)
				return {};
			MapIter mi;
			const char *name;
			TypeRange *member;
			long long below = 0;
			FOREACH_MAP_ITEM(members, mi, &name, &member) {
				if (next.node)
					below += member->NumElements(); // members after the match sit toward LSB
				else if (step.member == name) {
					next.node = member;
					next.span = member->NumElements();
				}
			}
			if (!next.node)
				return {};
			if (at.node->IsTypeVerilogUnion())
				below = 0; // every member overlays the whole union
			next.offset = at.offset + below;
			next.lsb_step = below == 0; // last declared member is the LSB end
		}
		points.push_back(next);
	}
	return points;
}

// Bits under points[depth]. obj is var plus every unpacked [i] down to there
std::optional<RtlBinder::Location> RtlBinder::locate(const std::string &var, const std::vector<WalkPoint> &points, size_t depth) const
{
	Location loc;
	loc.var = loc.obj = var;
	size_t anchor = 0;
	for (size_t k = 1; k <= depth && points[k].element; k++) {
		loc.obj += "[" + std::to_string(points[k].index) + "]"; // e.g. mem -> mem[3]
		anchor = k;
	}
	if (!decl_shape(points[depth].node, loc.shape) || loc.shape.width() != points[depth].span)
		return std::nullopt;
	loc.offset = points[depth].offset; // where this span sits in the variable
	loc.obj_offset = points[anchor].offset;
	loc.obj_width = points[anchor].span; // dump width of that unpacked element
	return loc;
}

// Verific left a trailing [a:b] on the name: shrink the top dimension to that range
bool RtlBinder::narrow(Location &loc, const TypeRange *node, int a, int b) const
{
	if (!node || !node->IsTypeArray())
		return false;
	int msb = node->LeftRangeBound(), lsb = node->RightRangeBound();
	int lo = std::min(msb, lsb), hi = std::max(msb, lsb);
	if (std::min(a, b) < lo || std::max(a, b) > hi)
		return false;
	bool packed = range_packed(node);
	long long width = hi - lo + 1, count = std::abs(a - b) + 1, sub = loc.shape.width() / width;
	// Verific keeps the range's indices in declared order from the range's own LSB
	long long first = packed ? std::min(std::abs(a - lsb), std::abs(b - lsb)) : hi - std::max(a, b);
	std::pair<int, int> &dim = packed ? loc.shape.packed.front() : loc.shape.unpacked.front();
	dim = msb >= lsb ? std::make_pair(std::max(a, b), std::min(a, b)) : std::make_pair(std::min(a, b), std::max(a, b));
	(packed ? loc.shape.packed_bits : loc.shape.elements) = (packed ? loc.shape.packed_bits : loc.shape.elements) / width * count;
	loc.offset += first * sub;
	return true;
}

// Turn a Verific primitive name + Q width into a Location, or nullopt
std::optional<RtlBinder::Location> RtlBinder::decode_register(const std::string &name, int q_width) const
{
	// `<path>_reg[i]...[k]`, optionally ending in `[a:b]`
	size_t marker = name.rfind("_reg");
	if (marker == std::string::npos || marker == 0)
		return std::nullopt;
	std::string tail = name.substr(marker + 4); // after `_reg`: extra [i]s
	size_t open = tail.rfind('['), colon = tail.rfind(':');
	bool ranged = open != std::string::npos && colon != std::string::npos && colon > open && tail.back() == ']';
	int a = 0, b = 0;
	if (ranged) {
		if (!parse_int(tail.substr(open + 1, colon - open - 1), a) || !parse_int(tail.substr(colon + 1, tail.size() - colon - 2), b))
			return std::nullopt;
		tail.resize(open); // strip the trailing [a:b], keep the [i]s
	}
	std::string var;
	std::vector<Step> steps, indices;
	const TypeRange *head = find_variable(name.substr(0, marker), var, steps); // left of `_reg`
	if (!head || !parse_steps(tail, 0, indices))
		return std::nullopt;
	for (auto &step : indices) {
		if (!step.is_index)
			return std::nullopt; // after `_reg` only [i], never .m
		steps.push_back(step);
	}
	std::vector<WalkPoint> points = walk(head, steps);
	if (points.empty())
		return std::nullopt;

	// Deepest walk point whose span is Q. Extra [0]s past that only name the LSB.
	size_t at = points.size();
	if (ranged)
		at = points.size() - 1; // [a:b] applies to the last remaining dimension
	else
		for (size_t k = points.size(); k-- > 0;) {
			if (points[k].span == q_width) {
				at = k;
				break;
			}
			if (!points[k].lsb_step)
				break; // a non-LSB index is a real slice, not a name suffix
		}
	if (at == points.size())
		return std::nullopt;
	std::optional<Location> loc = locate(var, points, at);
	if (!loc || (ranged && !narrow(*loc, points[at].node, a, b)) || loc->shape.width() != q_width)
		return std::nullopt;
	return loc;
}

// Same decode, but from a Q wire name (`foo`, `foo[3]`, `s.a`) instead of `foo_reg`
const RtlBinder::Location *RtlBinder::place_net(RTLIL::Wire *wire)
{
	if (!wire || !wire->name.isPublic())
		return nullptr;
	auto it = net_places.find(wire);
	if (it == net_places.end()) {
		std::string var;
		std::vector<Step> steps;
		std::optional<Location> loc;
		if (const TypeRange *head = find_variable(wire->name.unescape(), var, steps)) {
			std::vector<WalkPoint> points = walk(head, steps);
			if (!points.empty())
				loc = locate(var, points, points.size() - 1); // the wire is exactly the last step
		}
		it = net_places.emplace(wire, loc).first;
	}
	return it->second ? &*it->second : nullptr;
}

void RtlBinder::begin(Netlist *netlist)
{
	nl = netlist;
	vhdl = nl->IsFromVhdl();
	net_places.clear();
}

void RtlBinder::stamp(Instance *inst, const RTLIL::SigSpec &sig_q, const std::vector<RTLIL::Cell *> &cells)
{
	const int q_width = GetSize(sig_q);
	std::optional<Location> reg = decode_register(inst->Name(), q_width);

	// If Q drives a net of the same variable, that net's bit must match the name decode
	for (int b = 0; reg && b < q_width; b++) {
		const Location *net = place_net(sig_q[b].wire);
		if (!net || net->var != reg->var)
			continue;
		long long reg_bit = -1, net_bit = -1;
		reg->var_bit(b, reg_bit);
		if (!net->var_bit(sig_q[b].offset, net_bit) || net_bit != reg_bit) {
			log_warning("RTL bind of register %s rejected: Q bit %d decodes to %s bit %lld but drives %s[%d] (bit %lld)\n",
					inst->Name(), b, reg->var.c_str(), reg_bit, log_id(sig_q[b].wire), sig_q[b].offset, net_bit);
			reg.reset();
		}
	}

	// Name decode if it survived; else place each Q bit from the net it drives
	std::vector<RtlBindBit> binds(q_width);
	for (int b = 0; b < q_width; b++) {
		if (reg)
			binds[b] = reg->bind(b);
		else if (const Location *net = place_net(sig_q[b].wire))
			binds[b] = net->bind(sig_q[b].offset);
		(!binds[b].valid ? missing_bits : reg ? decoded_bits : fallback_bits)++;
	}

	int offset = 0;
	for (RTLIL::Cell *cell : cells) {
		int width = GetSize(cell->getPort(ID::Q));
		log_assert(offset + width <= q_width);
		cell->set_string_attribute(ID(rtl_bind), rtl_bind_compress({binds.begin() + offset, binds.begin() + offset + width}));
		offset += width;
	}
}

void RtlBinder::stamp(Instance *inst, RTLIL::Cell *cell)
{
	stamp(inst, cell->getPort(ID::Q), {cell});
}

void RtlBinder::finish(RTLIL::Module *module)
{
	if (decoded_bits || fallback_bits || missing_bits)
		log("  RTL bind of module %s: %d register bit(s) placed from their register name, %d from their net, %d unbound.\n",
				log_id(module->name), decoded_bits, fallback_bits, missing_bits);
	decoded_bits = fallback_bits = missing_bits = 0;
	net_places.clear();
}

#endif /* YOSYS_ENABLE_VERIFIC */
