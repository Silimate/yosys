/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  SILIMATE: RTL bind of Verific register primitives, see rtl_bind.cc
 */

#ifndef VERIFIC_RTL_BIND_H
#define VERIFIC_RTL_BIND_H

#include "kernel/yosys.h"
#include "kernel/ff.h"
#include <optional>

namespace Verific {
	class Netlist;
	class Instance;
	class TypeRange;
}

YOSYS_NAMESPACE_BEGIN

// Stamps the `rtl_bind` attribute (kernel/ff.h) on the cells imported for the register
// primitives of one netlist, decoding each primitive's name through the netlist's type ranges.
struct RtlBinder
{
	void begin(Verific::Netlist *nl);
	// Cells holding the Q bits of `inst` from offset 0 on, in order, or one cell holding all
	void stamp(Verific::Instance *inst, const RTLIL::SigSpec &sig_q, const std::vector<RTLIL::Cell *> &cells);
	void stamp(Verific::Instance *inst, RTLIL::Cell *cell);
	void finish(RTLIL::Module *module);

private:
	// One step below a variable: an array or packed index `[i]`, or a struct member `.m`
	struct Step {
		bool is_index = false;
		int index = 0;
		std::string member;
	};

	// Declared ranges below a type node, (msb, lsb) outermost first, split by dump behaviour
	struct Shape {
		std::vector<std::pair<int, int>> unpacked, packed;
		long long elements = 1, packed_bits = 1;
		long long width() const { return elements * packed_bits; }
		bool bit(long long flat, long long &dump) const;
	};

	// A node reached by walking steps: the bits below it, the variable bit of its LSB,
	// whether the step reached the least significant index/member, and the index if it
	// reached an unpacked element
	struct WalkPoint {
		const Verific::TypeRange *node = nullptr;
		long long span = 0, offset = 0;
		bool lsb_step = true;
		bool element = false;
		int index = 0;
	};

	// A bit span of a variable and the object (the variable or an unpacked element of it)
	// it is anchored at
	struct Location {
		std::string var, obj;
		Shape shape;
		long long offset = 0, obj_offset = 0, obj_width = 0;
		bool var_bit(long long b, long long &out) const;
		RtlBindBit bind(long long b) const;
	};

	Verific::Netlist *nl = nullptr;
	bool vhdl = false;
	std::map<RTLIL::Wire *, std::optional<Location>> net_places;
	std::map<std::string, std::string> flattened; // `q0_sel` -> `q0.sel`
	int decoded_bits = 0, fallback_bits = 0, missing_bits = 0;

	bool parse_steps(const std::string &path, size_t pos, std::vector<Step> &steps) const;
	const Verific::TypeRange *find_variable(const std::string &path, std::string &var, std::vector<Step> &steps) const;
	bool range_packed(const Verific::TypeRange *t) const;
	bool decl_shape(const Verific::TypeRange *tr, Shape &shape) const;
	std::vector<WalkPoint> walk(const Verific::TypeRange *head, const std::vector<Step> &steps) const;
	std::optional<Location> locate(const std::string &var, const std::vector<WalkPoint> &points, size_t depth) const;
	bool narrow(Location &loc, const Verific::TypeRange *node, int a, int b) const;
	std::optional<Location> decode_register(const std::string &name, int q_width) const;
	const Location *place_net(RTLIL::Wire *wire);
};

YOSYS_NAMESPACE_END

#endif
