/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *  Copyright (C) 2026  Silimate Inc.     <akash@silimate.com>
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
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHERWISE, ARISING OUT OF OR IN
 *  CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include <algorithm>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct OptAndOrPmuxWorker
{
	struct DriverBit {
		Cell *cell = nullptr;
		IdString port;
		int index = -1;
	};

	struct ConsumerBit {
		Cell *cell = nullptr;
		IdString port;
		int index = -1;
	};

	struct EqInfo {
		SigSpec select;
		Const value;
		SigBit bit;
	};

	struct DataExpr {
		std::vector<SigBit> factors;
	};

	struct Contribution {
		EqInfo eq;
		DataExpr data;
	};

	enum TermResult {
		TERM_FAIL,
		TERM_ZERO,
		TERM_OK,
		TERM_BUDGET,
	};

	enum WalkStatus {
		WALK_OK,
		WALK_FAIL,
		WALK_BUDGET,
	};

	enum ConvertStatus {
		CONVERT_NONE,
		CONVERT_OK,
		CONVERT_BUDGET,
	};

	struct Arm {
		Const value;
		SigBit select_bit;
		std::vector<std::vector<DataExpr>> bits;
	};

	struct BitContribs {
		int bit_idx = -1;
		SigSpec select;
		std::vector<Contribution> contribs;
	};

	struct SelectGroup {
		SigSpec select;
		std::vector<BitContribs> bits;
	};

	struct CachedTerm {
		TermResult result = TERM_FAIL;
		Contribution contrib;
	};

	Module *module;
	SigMap sigmap;

	dict<SigBit, DriverBit> bit_drivers;
	dict<SigBit, std::vector<ConsumerBit>> bit_consumers;
	pool<SigBit> observable_bits;
	// IdString, not Cell*: pool<Cell*> uses hash_obj_ops and breaks after remove().
	pool<IdString> removed_cell_names;

	// Memoize structural parses. Over-budget results are not cached so a
	// later retry with a larger cone cap can succeed.
	dict<SigBit, CachedTerm> term_cache;
	dict<SigBit, EqInfo> eq_cache;
	pool<SigBit> eq_negative_cache;

	int converted_count = 0;
	static const int probe_cone_bits = 64;
	static const int max_cone_bits = 100000;
	static const int large_cone_budget = 32;
	static const int min_pmux_bits = 8;

	OptAndOrPmuxWorker(Module *module) : module(module), sigmap(module)
	{
		run();
	}

	void build_maps()
	{
		bit_drivers.clear();
		bit_consumers.clear();
		observable_bits.clear();

		for (auto cell : module->cells())
		{
			for (auto &conn : cell->connections())
			{
				SigSpec sig = sigmap(conn.second);

				if (cell->output(conn.first)) {
					for (int i = 0; i < GetSize(sig); i++) {
						SigBit bit = sig[i];
						if (bit.wire == nullptr)
							continue;
						if (bit_drivers.count(bit))
							bit_drivers[bit].cell = nullptr;
						else
							bit_drivers[bit] = {cell, conn.first, i};
					}
				}

				if (cell->input(conn.first)) {
					for (int i = 0; i < GetSize(sig); i++) {
						SigBit bit = sig[i];
						if (bit.wire == nullptr)
							continue;
						bit_consumers[bit].push_back({cell, conn.first, i});
					}
				}
			}
		}

		for (auto &conn : module->connections())
		{
			SigSpec lhs = conn.first;
			SigSpec rhs = sigmap(conn.second);
			for (int i = 0; i < std::min(GetSize(lhs), GetSize(rhs)); i++) {
				SigBit lhs_bit = lhs[i];
				SigBit rhs_bit = rhs[i];
				if (lhs_bit.wire == nullptr)
					continue;
				if (lhs_bit.wire->port_output || lhs_bit.wire->get_bool_attribute(ID::keep)) {
					observable_bits.insert(lhs_bit);
					observable_bits.insert(rhs_bit);
				}
			}
		}
	}

	bool get_driver(SigBit bit, DriverBit &driver) const
	{
		bit = sigmap(bit);
		auto it = bit_drivers.find(bit);
		if (it == bit_drivers.end() || it->second.cell == nullptr)
			return false;
		driver = it->second;
		return true;
	}

	bool get_input_bit(Cell *cell, IdString port, int index, SigBit &bit) const
	{
		SigSpec sig = sigmap(cell->getPort(port));
		if (index < 0 || index >= GetSize(sig))
			return false;
		bit = sig[index];
		return true;
	}

	bool bit_has_observable_output(SigBit bit) const
	{
		bit = sigmap(bit);
		if (bit.wire == nullptr)
			return false;
		if (bit.wire->port_output || bit.wire->get_bool_attribute(ID::keep))
			return true;
		if (observable_bits.count(bit))
			return true;
		auto it = bit_consumers.find(bit);
		if (it != bit_consumers.end())
			return !it->second.empty();
		return false;
	}

	bool cell_has_observable_output(Cell *cell) const
	{
		for (auto bit : sigmap(cell->getPort(ID::Y)))
			if (bit_has_observable_output(bit))
				return true;
		return false;
	}

	// Drop a cell from the driver/consumer indexes before module->remove so
	// later candidates do not touch freed Cell* entries (hash_obj_ops).
	void erase_cell(Cell *cell)
	{
		for (auto &conn : cell->connections()) {
			SigSpec sig = sigmap(conn.second);
			if (cell->output(conn.first)) {
				for (int i = 0; i < GetSize(sig); i++) {
					SigBit bit = sig[i];
					if (bit.wire == nullptr)
						continue;
					auto it = bit_drivers.find(bit);
					if (it != bit_drivers.end() && it->second.cell == cell)
						bit_drivers.erase(it);
				}
			}
			if (cell->input(conn.first)) {
				for (auto bit : sig) {
					if (bit.wire == nullptr)
						continue;
					auto it = bit_consumers.find(bit);
					if (it == bit_consumers.end())
						continue;
					auto &vec = it->second;
					vec.erase(std::remove_if(vec.begin(), vec.end(),
							[&](const ConsumerBit &c) { return c.cell == cell; }),
							vec.end());
					if (vec.empty())
						bit_consumers.erase(it);
				}
			}
		}
		removed_cell_names.insert(cell->name);
		module->remove(cell);
	}

	// Cheap reject: a decode OR must fan into $and/$eq/$or somewhere nearby.
	bool cell_looks_interesting(Cell *cell) const
	{
		for (auto port : {ID::A, ID::B}) {
			SigSpec sig = sigmap(cell->getPort(port));
			for (auto bit : sig) {
				if (bit.wire == nullptr)
					continue;
				DriverBit driver;
				if (!get_driver(bit, driver))
					continue;
				if (driver.cell->type.in(ID($and), ID($or), ID($eq)))
					return true;
			}
		}
		return false;
	}

	// Prefer OR roots (non-OR consumers / ports) over internal reduction nodes.
	int candidate_rank(Cell *cell) const
	{
		SigSpec y = sigmap(cell->getPort(ID::Y));
		bool saw_non_or_consumer = false;
		bool saw_port = false;
		for (auto bit : y) {
			if (bit.wire == nullptr)
				continue;
			if (bit.wire->port_output || bit.wire->get_bool_attribute(ID::keep) || observable_bits.count(bit))
				saw_port = true;
			auto it = bit_consumers.find(bit);
			if (it == bit_consumers.end())
				continue;
			for (auto &consumer : it->second) {
				if (consumer.cell->type != ID($or))
					saw_non_or_consumer = true;
			}
		}
		if (saw_port || saw_non_or_consumer)
			return 0;
		return 1;
	}

	bool match_eq(SigBit bit, EqInfo &eq)
	{
		bit = sigmap(bit);
		if (eq_negative_cache.count(bit))
			return false;
		auto cached = eq_cache.find(bit);
		if (cached != eq_cache.end()) {
			eq = cached->second;
			return true;
		}

		DriverBit driver;
		if (!get_driver(bit, driver)) {
			eq_negative_cache.insert(bit);
			return false;
		}

		Cell *cell = driver.cell;
		if (driver.port != ID::Y || driver.index != 0 || cell->type != ID($eq)) {
			eq_negative_cache.insert(bit);
			return false;
		}

		SigSpec nonconst_sig = sigmap(cell->getPort(ID::A));
		SigSpec const_sig = sigmap(cell->getPort(ID::B));

		if (!const_sig.is_fully_const()) {
			if (!nonconst_sig.is_fully_const()) {
				eq_negative_cache.insert(bit);
				return false;
			}
			std::swap(nonconst_sig, const_sig);
		}

		if (nonconst_sig.empty() || const_sig.empty() || nonconst_sig.is_fully_const()) {
			eq_negative_cache.insert(bit);
			return false;
		}

		eq.select = nonconst_sig;
		eq.value = const_sig.as_const();
		eq.bit = bit;
		eq_cache[bit] = eq;
		return true;
	}

	WalkStatus collect_or_terms(SigBit bit, std::vector<SigBit> &terms, pool<SigBit> &seen, int &budget) const
	{
		if (--budget < 0)
			return WALK_BUDGET;

		bit = sigmap(bit);

		if (bit == State::S0 || bit == State::Sx || bit == State::Sz)
			return WALK_OK;
		if (bit == State::S1)
			return WALK_FAIL;

		if (!seen.insert(bit).second)
			return WALK_FAIL;

		DriverBit driver;
		if (get_driver(bit, driver) && driver.port == ID::Y && driver.cell->type == ID($or)) {
			SigBit a, b;
			if (!get_input_bit(driver.cell, ID::A, driver.index, a))
				return WALK_FAIL;
			if (!get_input_bit(driver.cell, ID::B, driver.index, b))
				return WALK_FAIL;
			WalkStatus sa = collect_or_terms(a, terms, seen, budget);
			if (sa != WALK_OK)
				return sa;
			return collect_or_terms(b, terms, seen, budget);
		}

		terms.push_back(bit);
		return WALK_OK;
	}

	WalkStatus collect_and_factors(SigBit bit, std::vector<SigBit> &factors, pool<SigBit> &seen, int &budget) const
	{
		if (--budget < 0)
			return WALK_BUDGET;

		bit = sigmap(bit);

		if (bit == State::S0 || bit == State::S1 || bit == State::Sx || bit == State::Sz) {
			factors.push_back(bit);
			return WALK_OK;
		}

		if (!seen.insert(bit).second)
			return WALK_FAIL;

		DriverBit driver;
		if (get_driver(bit, driver) && driver.port == ID::Y && driver.cell->type == ID($and)) {
			SigBit a, b;
			if (!get_input_bit(driver.cell, ID::A, driver.index, a))
				return WALK_FAIL;
			if (!get_input_bit(driver.cell, ID::B, driver.index, b))
				return WALK_FAIL;
			WalkStatus sa = collect_and_factors(a, factors, seen, budget);
			if (sa != WALK_OK)
				return sa;
			return collect_and_factors(b, factors, seen, budget);
		}

		factors.push_back(bit);
		return WALK_OK;
	}

	TermResult parse_term(SigBit bit, Contribution &contrib, int cone_budget)
	{
		bit = sigmap(bit);
		auto cached = term_cache.find(bit);
		if (cached != term_cache.end()) {
			contrib = cached->second.contrib;
			return cached->second.result;
		}

		EqInfo direct_eq;
		if (match_eq(bit, direct_eq)) {
			contrib.eq = direct_eq;
			contrib.data.factors.clear();
			term_cache[bit] = {TERM_OK, contrib};
			return TERM_OK;
		}

		std::vector<SigBit> factors;
		pool<SigBit> seen;
		int budget = cone_budget;
		WalkStatus walk = collect_and_factors(bit, factors, seen, budget);
		if (walk == WALK_BUDGET)
			return TERM_BUDGET;
		if (walk != WALK_OK) {
			term_cache[bit] = {TERM_FAIL, Contribution()};
			return TERM_FAIL;
		}

		Contribution parsed;
		bool have_eq = false;
		for (auto factor : factors)
		{
			factor = sigmap(factor);
			if (factor == State::S0) {
				term_cache[bit] = {TERM_ZERO, Contribution()};
				return TERM_ZERO;
			}
			if (factor == State::Sx || factor == State::Sz) {
				term_cache[bit] = {TERM_FAIL, Contribution()};
				return TERM_FAIL;
			}
			if (factor == State::S1)
				continue;

			EqInfo eq;
			if (match_eq(factor, eq)) {
				if (!have_eq) {
					parsed.eq = eq;
					have_eq = true;
				} else if (parsed.eq.select != eq.select || parsed.eq.value != eq.value) {
					term_cache[bit] = {TERM_FAIL, Contribution()};
					return TERM_FAIL;
				}
				continue;
			}

			parsed.data.factors.push_back(factor);
		}

		if (!have_eq) {
			term_cache[bit] = {TERM_FAIL, Contribution()};
			return TERM_FAIL;
		}

		contrib = parsed;
		term_cache[bit] = {TERM_OK, contrib};
		return TERM_OK;
	}

	SigBit make_and_tree(Cell *cell, const std::vector<SigBit> &factors, const std::string &src)
	{
		SigBit result = State::S1;

		for (auto factor : factors)
		{
			factor = sigmap(factor);
			if (factor == State::S0 || factor == State::Sx || factor == State::Sz)
				return State::S0;
			if (factor == State::S1)
				continue;
			if (result == State::S1) {
				result = factor;
				continue;
			}

			Wire *wire = module->addWire(NEW_ID2_SUFFIX("andor_pmux_data_and"), 1);
			module->addAnd(NEW_ID2_SUFFIX("andor_pmux_data_and"), result, factor, SigBit(wire), false, src);
			result = SigBit(wire);
		}

		return result;
	}

	SigBit make_or_tree(Cell *cell, const std::vector<SigBit> &terms, const std::string &src)
	{
		SigBit result = State::S0;

		for (auto term : terms)
		{
			term = sigmap(term);
			if (term == State::S1)
				return State::S1;
			if (term == State::S0 || term == State::Sx || term == State::Sz)
				continue;
			if (result == State::S0) {
				result = term;
				continue;
			}

			Wire *wire = module->addWire(NEW_ID2_SUFFIX("andor_pmux_data_or"), 1);
			module->addOr(NEW_ID2_SUFFIX("andor_pmux_data_or"), result, term, SigBit(wire), false, src);
			result = SigBit(wire);
		}

		return result;
	}

	SigBit emit_data_bit(Cell *cell, const std::vector<DataExpr> &exprs, const std::string &src)
	{
		std::vector<SigBit> terms;
		for (auto &expr : exprs) {
			SigBit term = make_and_tree(cell, expr.factors, src);
			if (term == State::S1)
				return State::S1;
			if (term != State::S0 && term != State::Sx && term != State::Sz)
				terms.push_back(term);
		}
		return make_or_tree(cell, terms, src);
	}

	// Tiny fanin peek: reject AND/OR cones that never touch $eq before we
	// spend the full cone budget expanding them. Visit OR/AND siblings
	// before deeper spines so skewed reduction trees still find $eq leaves.
	bool peek_has_eq(SigBit root, int budget) const
	{
		pool<SigBit> seen;
		std::vector<SigBit> work = {sigmap(root)};
		while (!work.empty()) {
			if (--budget < 0)
				return false;
			SigBit bit = work.back();
			work.pop_back();
			if (bit.wire == nullptr)
				continue;
			if (!seen.insert(bit).second)
				continue;

			DriverBit driver;
			if (!get_driver(bit, driver) || driver.port != ID::Y)
				continue;
			if (driver.cell->type == ID($eq))
				return driver.index == 0;
			if (!driver.cell->type.in(ID($and), ID($or)))
				continue;

			SigBit a, b;
			if (!get_input_bit(driver.cell, ID::A, driver.index, a))
				continue;
			if (!get_input_bit(driver.cell, ID::B, driver.index, b))
				continue;
			work.push_back(a);
			work.push_back(b);
		}
		return false;
	}

	ConvertStatus collect_bit_contribs(Cell *cell, int bit_idx, BitContribs &bit_contribs, int cone_budget)
	{
		SigSpec y = sigmap(cell->getPort(ID::Y));
		SigBit y_bit = y[bit_idx];

		if (!bit_has_observable_output(y_bit))
			return CONVERT_NONE;
		if (!peek_has_eq(y_bit, std::min(cone_budget, 128)))
			return CONVERT_NONE;

		std::vector<SigBit> terms;
		pool<SigBit> seen;
		int budget = cone_budget;
		WalkStatus walk = collect_or_terms(y_bit, terms, seen, budget);
		if (walk == WALK_BUDGET)
			return CONVERT_BUDGET;
		if (walk != WALK_OK)
			return CONVERT_NONE;

		bit_contribs.bit_idx = bit_idx;
		for (auto term : terms)
		{
			Contribution contrib;
			TermResult result = parse_term(term, contrib, cone_budget);
			if (result == TERM_BUDGET)
				return CONVERT_BUDGET;
			if (result == TERM_ZERO)
				continue;
			if (result == TERM_FAIL)
				return CONVERT_NONE;

			if (bit_contribs.select.empty())
				bit_contribs.select = contrib.eq.select;
			else if (bit_contribs.select != contrib.eq.select)
				return CONVERT_NONE;

			bit_contribs.contribs.push_back(contrib);
		}

		return bit_contribs.contribs.empty() ? CONVERT_NONE : CONVERT_OK;
	}

	bool convert_group(Cell *cell, const SelectGroup &group, pool<int> &converted_bits)
	{
		SigSpec y = sigmap(cell->getPort(ID::Y));
		int width = GetSize(group.bits);
		if (width == 0)
			return false;

		std::vector<Arm> arms;
		dict<Const, int> arm_index;

		for (int group_bit_idx = 0; group_bit_idx < width; group_bit_idx++)
		{
			const BitContribs &bit_contribs = group.bits[group_bit_idx];
			for (auto &contrib : bit_contribs.contribs)
			{
				int arm_idx;
				auto it = arm_index.find(contrib.eq.value);
				if (it == arm_index.end()) {
					arm_idx = GetSize(arms);
					arms.push_back({contrib.eq.value, contrib.eq.bit, std::vector<std::vector<DataExpr>>(width)});
					arm_index[contrib.eq.value] = arm_idx;
				} else {
					arm_idx = it->second;
				}

				arms[arm_idx].bits[group_bit_idx].push_back(contrib.data);
			}
		}

		if (GetSize(arms) < 2 || GetSize(arms) * width < min_pmux_bits)
			return false;

		SigSpec pmux_y, pmux_s, pmux_b;
		std::string src = cell->get_src_attribute();

		for (auto &bit_contribs : group.bits)
			pmux_y.append(y[bit_contribs.bit_idx]);

		for (auto &arm : arms)
		{
			SigSpec data;
			for (int bit_idx = 0; bit_idx < width; bit_idx++)
				data.append(emit_data_bit(cell, arm.bits[bit_idx], src));

			pmux_b.append(data);
			pmux_s.append(arm.select_bit);
		}

		log("Converting AND/OR mux %s.%s to a $pmux with %d cases and width %d.\n",
				log_id(module), log_id(cell), GetSize(arms), width);

		module->addPmux(NEW_ID2_SUFFIX("andor_pmux"), Const(State::S0, width), pmux_b, pmux_s, pmux_y, src);
		for (auto &bit_contribs : group.bits)
			converted_bits.insert(bit_contribs.bit_idx);
		converted_count++;
		return true;
	}

	ConvertStatus try_convert(Cell *cell, int cone_budget)
	{
		if (removed_cell_names.count(cell->name))
			return CONVERT_NONE;
		if (cell->type != ID($or) || cell->get_bool_attribute(ID::keep))
			return CONVERT_NONE;
		if (!cell_has_observable_output(cell))
			return CONVERT_NONE;

		SigSpec y = sigmap(cell->getPort(ID::Y));
		SigSpec a = sigmap(cell->getPort(ID::A));
		SigSpec b = sigmap(cell->getPort(ID::B));
		int width = GetSize(y);
		if (width == 0)
			return CONVERT_NONE;

		std::vector<SelectGroup> groups;
		dict<SigSpec, int> group_index;
		bool hit_budget = false;

		for (int bit_idx = 0; bit_idx < width; bit_idx++)
		{
			BitContribs bit_contribs;
			ConvertStatus st = collect_bit_contribs(cell, bit_idx, bit_contribs, cone_budget);
			if (st == CONVERT_BUDGET) {
				hit_budget = true;
				continue;
			}
			if (st != CONVERT_OK)
				continue;

			auto git = group_index.find(bit_contribs.select);
			if (git == group_index.end()) {
				group_index[bit_contribs.select] = GetSize(groups);
				groups.push_back({bit_contribs.select, {bit_contribs}});
			} else {
				groups[git->second].bits.push_back(bit_contribs);
			}
		}

		// On the probe pass, any over-budget bit forces a full rewalk so a
		// wide select group is not partially committed before all bits parse.
		if (hit_budget && cone_budget < max_cone_bits)
			return CONVERT_BUDGET;

		pool<int> converted_bits;
		for (auto &group : groups)
			convert_group(cell, group, converted_bits);

		if (converted_bits.empty())
			return hit_budget ? CONVERT_BUDGET : CONVERT_NONE;

		SigSpec keep_a, keep_b, keep_y;
		for (int bit_idx = 0; bit_idx < width; bit_idx++) {
			if (converted_bits.count(bit_idx))
				continue;
			keep_a.append(a[bit_idx]);
			keep_b.append(b[bit_idx]);
			keep_y.append(y[bit_idx]);
		}

		std::string src = cell->get_src_attribute();
		if (!keep_y.empty())
			module->addOr(NEW_ID2_SUFFIX("andor_pmux_keep_or"), keep_a, keep_b, keep_y, false, src);
		erase_cell(cell);

		return CONVERT_OK;
	}

	void run()
	{
		build_maps();

		struct Cand {
			Cell *cell;
			IdString name;
			int width;
		};
		std::vector<Cand> cands;

		for (auto cell : module->selected_cells()) {
			if (cell->type != ID($or) || cell->get_bool_attribute(ID::keep))
				continue;
			SigSpec y = sigmap(cell->getPort(ID::Y));
			if (y.empty())
				continue;
			if (!cell_has_observable_output(cell))
				continue;
			if (!cell_looks_interesting(cell))
				continue;
			// Skip pure OR-reduction internals: converting a parent root leaves
			// the dead spine interconnected, so internals would still look
			// "live" and emit duplicate smaller $pmux cells.
			if (candidate_rank(cell) != 0)
				continue;
			cands.push_back({cell, cell->name, GetSize(y)});
		}

		// Wider roots first so a multi-bit select group is preferred over a
		// narrower alias of the same cone. Name tie-break keeps order stable.
		std::sort(cands.begin(), cands.end(), [](const Cand &a, const Cand &b) {
			if (a.width != b.width)
				return a.width > b.width;
			return a.name.str() < b.name.str();
		});

		int large_left = large_cone_budget;
		for (auto &cand : cands) {
			if (removed_cell_names.count(cand.name))
				continue;

			ConvertStatus st = try_convert(cand.cell, probe_cone_bits);
			if (st == CONVERT_OK)
				continue;
			if (st != CONVERT_BUDGET)
				continue;

			if (large_left <= 0)
				continue;
			large_left--;
			try_convert(cand.cell, max_cone_bits);
		}
	}
};

struct OptAndOrPmuxPass : public Pass {
	OptAndOrPmuxPass() : Pass("opt_andor_pmux", "convert equality-decoded AND/OR muxes to $pmux") { }

	void help() override
	{
		log("\n");
		log("    opt_andor_pmux [selection]\n");
		log("\n");
		log("This pass converts logic of the form:\n");
		log("\n");
		log("    (sel == C0 & D0) | (sel == C1 & D1) | ...\n");
		log("\n");
		log("into $pmux cells. It only rewrites terms whose select conditions are\n");
		log("equality comparisons against distinct constants of the same select signal.\n");
		log("Very small conversions are ignored to avoid replacing tiny boolean cones.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_ANDOR_PMUX pass (AND/OR muxes to $pmux).\n");

		size_t argidx = 1;
		extra_args(args, argidx, design);

		int total_converted = 0;
		for (auto module : design->selected_modules()) {
			OptAndOrPmuxWorker worker(module);
			total_converted += worker.converted_count;
		}

		if (total_converted)
			design->scratchpad_set_bool("opt.did_something", true);

		log("Converted %d AND/OR muxes to $pmux cells.\n", total_converted);
	}
} OptAndOrPmuxPass;

PRIVATE_NAMESPACE_END
