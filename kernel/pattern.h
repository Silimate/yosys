#ifndef OPT_DFF_COMP_H
#define OPT_DFF_COMP_H

#include "kernel/rtlil.h"
#include <map>
#include <optional>
#include <set>

YOSYS_NAMESPACE_BEGIN

/**
 *  Pattern matching utilities for control signal analysis.
 *
 *  A pattern_t maps control signals to required values, representing a
 *  product term (conjunction): {A=1, B=0} means "A AND !B".
 *
 *  A patterns_t is a set of patterns representing a sum-of-products:
 *  {{A=1, B=0}, {A=0, C=1}} means "(A AND !B) OR (!A AND C)".
 *
 *  Used for analyzing MUX tree control paths in DFF optimization.
 */

// SILIMATE: Orders control bits by wire name, digit runs by value. IdString's operator< follows
// interning order, and plain string order flips when an $auto$ index gains a digit, so either would
// make the emitted logic depend on what else the process has read.
struct sort_ctrl_by_name {
	static int name_cmp(const char *a, const char *b) {
		const char *a0 = a, *b0 = b;
		while (*a && *b) {
			if (isdigit((unsigned char)*a) && isdigit((unsigned char)*b)) {
				while (*a == '0') a++;
				while (*b == '0') b++;
				size_t la = 0, lb = 0;
				while (isdigit((unsigned char)a[la])) la++;
				while (isdigit((unsigned char)b[lb])) lb++;
				if (la != lb)
					return la < lb ? -1 : 1;
				if (int c = strncmp(a, b, la))
					return c;
				a += la, b += lb;
			} else if (*a != *b) {
				return (unsigned char)*a < (unsigned char)*b ? -1 : 1;
			} else {
				a++, b++;
			}
		}
		if (*a || *b)
			return *a ? 1 : -1;
		return strcmp(a0, b0);
	}
	bool operator()(bool a, bool b) const { return a < b; }
	bool operator()(const RTLIL::SigBit &a, const RTLIL::SigBit &b) const {
		if (a.wire == b.wire)
			return a.wire ? a.offset < b.offset : a.data < b.data;
		if (!a.wire || !b.wire)
			return !a.wire;
		int c = name_cmp(a.wire->name.c_str(), b.wire->name.c_str());
		return c ? c < 0 : std::less<RTLIL::Wire *>()(a.wire, b.wire);
	}
	template<typename A, typename B> bool operator()(const std::pair<A, B> &a, const std::pair<A, B> &b) const {
		return (*this)(a.first, b.first) || (!(*this)(b.first, a.first) && (*this)(a.second, b.second));
	}
	template<typename T, typename C> bool operator()(const std::set<T, C> &a, const std::set<T, C> &b) const {
		return std::lexicographical_compare(a.begin(), a.end(), b.begin(), b.end(), *this);
	}
	template<typename K, typename V, typename C> bool operator()(const std::map<K, V, C> &a, const std::map<K, V, C> &b) const {
		return std::lexicographical_compare(a.begin(), a.end(), b.begin(), b.end(), *this);
	}
};

// Pattern matching for clock enable
// A pattern maps control signals to their required values for a MUX path
typedef std::map<RTLIL::SigBit, bool, sort_ctrl_by_name> pattern_t; // Set of control signals that must ALL match required vals
typedef std::set<pattern_t, sort_ctrl_by_name> patterns_t;          // Alternative patterns (OR)
typedef std::pair<RTLIL::SigBit, bool> ctrl_t;                      // Control signal
typedef std::set<ctrl_t, sort_ctrl_by_name> ctrls_t;                // Set of control signals that must ALL be active

/**
 * Find if two patterns differ in exactly one variable.
 * Example: {A=1,B=1} vs {A=1,B=0} returns B, allows simplification: (A&B) | (A&!B) => A
 */
inline std::optional<RTLIL::SigBit> find_complementary_pattern_var(
	const pattern_t& left,
	const pattern_t& right
) {
	std::optional<RTLIL::SigBit> ret;
	for (const auto &pt : left) {
		// Left requires signal that right doesn't constrain - incompatible domains
		if (right.count(pt.first) == 0)
			return std::nullopt;
		// Signal has same required value in both - not the complement variable
		if (right.at(pt.first) == pt.second)
			continue;
		// Already found one differing signal, now found another - not simplifiable
		if (ret)
			return std::nullopt;
		// First differing signal - candidate complement variable
		ret = pt.first;
	}
	return ret;
}

/**
 * Simplify a sum-of-products by merging complementary patterns: (A&B) | (A&!B) => A,
 * and removing redundant patterns: A | (A&B) => A
 */
inline void simplify_patterns(patterns_t& patterns) {
	auto new_patterns = patterns;

	// Merge complementary patterns
	bool optimized;
	do {
		optimized = false;
		for (auto i = patterns.begin(); i != patterns.end(); i++) {
			for (auto j = std::next(i, 1); j != patterns.end(); j++) {
				const auto& left = (GetSize(*j) <= GetSize(*i)) ? *j : *i;
				auto right = (GetSize(*i) < GetSize(*j)) ? *j : *i;
				const auto complementary_var = find_complementary_pattern_var(left, right);

				if (complementary_var && new_patterns.count(right)) {
					new_patterns.erase(right);
					right.erase(complementary_var.value());
					new_patterns.insert(right);
					optimized = true;
				}
			}
		}
		patterns = new_patterns;
	} while(optimized);

	// Remove redundant patterns
	for (auto i = patterns.begin(); i != patterns.end(); ++i) {
		for (auto j = std::next(i, 1); j != patterns.end(); ++j) {
			const auto& left = (GetSize(*j) <= GetSize(*i)) ? *j : *i;
			const auto& right = (GetSize(*i) < GetSize(*j)) ? *j : *i;
			bool redundant = true;

			for (const auto& pt : left)
				if (right.count(pt.first) == 0 || right.at(pt.first) != pt.second)
					redundant = false;
			if (redundant)
				new_patterns.erase(right);
		}
	}

	patterns = std::move(new_patterns);
}

YOSYS_NAMESPACE_END

#endif
