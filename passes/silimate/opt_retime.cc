/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Silimate Inc.
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
#include "kernel/sigtools.h"
#include "kernel/ff.h"
#include "kernel/celltypes.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool is_buf(Cell *cell)
{
	return cell->type.in(ID($buf), ID($_BUF_));
}

// Data input ports of a cell a register can be moved across, in port order. An
// empty list means the type is not supported as a cut.
//
// For any pure function f, f(reg(x1), .., reg(xn)) equals reg(f(x1, .., xn)) as
// long as every input is registered on the same clock, so what matters is the
// port list and not what the cell computes. Retiming does not care whether the
// operator commutes ($sub follows $add), how wide Y is next to A and B (a
// reduction narrows the register, a carry-out widens it), or whether a port is
// conventionally called control: a $mux select is listed here because
// reg(S) ? reg(B) : reg(A) equals reg(S ? B : A) only when S is registered too.
//
// The same holds for $logic_and, $eqx, $neg and so on: one entry each, left out
// until something tests them.
std::vector<IdString> data_inputs(Cell *cell)
{
	if (cell->type.in(ID($buf), ID($_BUF_)))
		return {ID::A};
	if (cell->type.in(ID($add), ID($sub), ID($and), ID($or), ID($xor), ID($xnor),
			ID($eq), ID($ne), ID($lt), ID($le), ID($gt), ID($ge),
			ID($shl), ID($shr)))
		return {ID::A, ID::B};
	if (cell->type.in(ID($not), ID($reduce_and), ID($reduce_or), ID($reduce_xor),
			ID($reduce_xnor), ID($reduce_bool)))
		return {ID::A};
	if (cell->type == ID($mux))
		return {ID::A, ID::B, ID::S};
	return {};
}

bool is_data_input(Cell *cell, IdString port)
{
	for (auto candidate : data_inputs(cell))
		if (candidate == port)
			return true;
	return false;
}

// One cell on the path between the flop and the cut, plus the data input the
// path enters it on. That is always A for a single-input cell; for $add the
// path may run through either operand, and for $mux through the select as well.
struct ChainStep {
	Cell *cell;
	IdString port;
};

// A register on a data input of a chain cell that a forward move folds into the
// single register the move leaves behind. If keep is set, the flop still has
// other readers, so the cut is rewired to D but the flop itself stays.
struct Merge {
	Cell *flop;
	Cell *cell;
	IdString port;
	SigSpec sig_d;
	bool keep;
};

struct CellPort {
	Cell *cell;
	IdString port;
};

pool<SigBit> wire_bits(const SigSpec &sig)
{
	pool<SigBit> bits;
	for (auto bit : sig) {
		if (!bit.is_wire())
			log_cmd_error("Retiming signal %s contains a constant bit.\n", log_signal(sig));
		bits.insert(bit);
	}
	return bits;
}

bool bits_overlap(const pool<SigBit> &bits, const SigSpec &sig)
{
	for (auto bit : sig)
		if (bit.is_wire() && bits.count(bit))
			return true;
	return false;
}

// Full-signal cell readers of sig, plus whether any bit is a partial cell
// read or a module output. unique_reader is the case of exactly one full
// reader and neither of the extras.
void scan_readers(Module *module, SigMap &sigmap, const SigSpec &sig,
		std::vector<CellPort> &full, bool &partial, bool &output)
{
	pool<SigBit> bits = wire_bits(sig);
	full.clear();
	partial = false;
	output = false;

	for (auto cell : module->cells()) {
		for (auto &conn : cell->connections()) {
			if (!cell->input(conn.first))
				continue;
			bool any = false;
			for (auto bit : sigmap(conn.second)) {
				if (bits.count(bit)) {
					any = true;
					break;
				}
			}
			if (!any)
				continue;
			if (sigmap(conn.second) == sig)
				full.push_back({cell, conn.first});
			else
				partial = true;
		}
	}
	for (auto wire : module->wires()) {
		if (!wire->port_output)
			continue;
		for (auto bit : sigmap(SigSpec(wire))) {
			if (bits.count(bit)) {
				output = true;
				break;
			}
		}
	}
}

Cell *unique_reader(Module *module, SigMap &sigmap, const SigSpec &sig, IdString &port)
{
	std::vector<CellPort> full;
	bool partial = false, output = false;
	scan_readers(module, sigmap, sig, full, partial, output);
	if (partial || output || GetSize(full) != 1) {
		port = IdString();
		return nullptr;
	}
	port = full[0].port;
	return full[0].cell;
}

// Walk the unique after-path of start.Y looking for cut. Used to pick which
// reader of a multi-fanout flop is the one the move follows; the first hop
// itself is allowed to share the flop's Q with other readers.
bool reaches_cut(Module *module, SigMap &sigmap, Cell *start, Cell *cut)
{
	if (start == cut)
		return true;
	if (!start->hasPort(ID::Y))
		return false;

	pool<Cell *> seen;
	seen.insert(start);
	SigSpec cur = sigmap(start->getPort(ID::Y));
	while (true) {
		IdString port;
		Cell *next = unique_reader(module, sigmap, cur, port);
		if (!next || !is_data_input(next, port))
			return false;
		if (seen.count(next))
			return false;
		seen.insert(next);
		if (next == cut)
			return true;
		if (!next->hasPort(ID::Y))
			return false;
		cur = sigmap(next->getPort(ID::Y));
	}
}

// True when `to` sits on the unique after-path of `from`. A leftover copy of
// a flop keeps the original D, so a move that would rewrite a cut feeding
// that D cannot leave the copy behind.
bool signal_reaches(Module *module, SigMap &sigmap, const SigSpec &from, const SigSpec &to)
{
	pool<Cell *> seen;
	SigSpec cur = sigmap(from);
	SigSpec target = sigmap(to);
	while (true) {
		if (cur == target)
			return true;
		IdString port;
		Cell *next = unique_reader(module, sigmap, cur, port);
		if (!next || !next->hasPort(ID::Y))
			return false;
		if (seen.count(next))
			return false;
		seen.insert(next);
		cur = sigmap(next->getPort(ID::Y));
	}
}

Cell *unique_driver(Module *module, SigMap &sigmap, const SigSpec &sig, IdString &port)
{
	dict<SigBit, pair<Cell *, IdString>> drivers;
	for (auto cell : module->cells()) {
		for (auto &conn : cell->connections()) {
			if (!cell->output(conn.first))
				continue;
			SigSpec mapped = sigmap(conn.second);
			for (int i = 0; i < GetSize(mapped); i++) {
				if (mapped[i].is_wire())
					drivers[mapped[i]] = {cell, conn.first};
			}
		}
	}

	Cell *found = nullptr;
	port = IdString();
	for (auto bit : sig) {
		auto it = drivers.find(bit);
		if (it == drivers.end())
			return nullptr;
		if (found && (it->second.first != found || it->second.second != port))
			return nullptr;
		found = it->second.first;
		port = it->second.second;
	}
	if (!found || sigmap(found->getPort(port)) != sig)
		return nullptr;
	return found;
}

std::vector<ChainStep> collect_chain(Module *module, SigMap &sigmap, Cell *flop, Cell *cut)
{
	std::vector<ChainStep> chain;
	pool<Cell *> seen;
	SigSpec q = sigmap(flop->getPort(ID::Q));

	// Only the full readers matter here, because all this has to settle is
	// which one the move follows to the cut. A partial read or a module
	// output on Q does not change that answer, it only means a copy has to
	// be left behind, which is apply_move's decision to make.
	std::vector<CellPort> full;
	bool partial = false, output = false;
	scan_readers(module, sigmap, q, full, partial, output);
	(void)partial;
	(void)output;

	ChainStep first = {};
	int paths = 0;
	for (auto &reader : full) {
		if (!is_data_input(reader.cell, reader.port))
			continue;
		if (!reaches_cut(module, sigmap, reader.cell, cut))
			continue;
		paths++;
		first = {reader.cell, reader.port};
	}
	if (paths == 0)
		log_cmd_error("Cut %s is not on the after-path of flop %s.\n", log_id(cut), log_id(flop));
	if (paths > 1)
		log_cmd_error("Cut %s is reachable from flop %s on more than one path.\n",
				log_id(cut), log_id(flop));

	seen.insert(first.cell);
	chain.push_back(first);
	if (first.cell == cut)
		return chain;

	SigSpec cur = sigmap(first.cell->getPort(ID::Y));
	while (true) {
		IdString port;
		Cell *next = unique_reader(module, sigmap, cur, port);
		if (!next || !is_data_input(next, port))
			break;

		if (seen.count(next))
			log_cmd_error("Cycle on the after-path of flop %s.\n", log_id(flop));
		seen.insert(next);
		chain.push_back({next, port});
		if (next == cut)
			break;
		cur = sigmap(next->getPort(ID::Y));
	}

	if (chain.back().cell != cut)
		log_cmd_error("Cut %s is not on the after-path of flop %s.\n", log_id(cut), log_id(flop));
	return chain;
}

// Controls a move cannot relocate. Both of these load a value into the register
// from a net rather than from a parameter, so carrying them across a cut would
// mean building logic to transform that net rather than folding a constant.
//
// A clock enable is deliberately absent: it stores no value of its own, it only
// decides whether the register updates. Holding commutes with a pure function,
// since f of an unchanged input is an unchanged f, so the enable travels with
// the register untouched.
const char *unmovable_reason(FfData &ff)
{
	if (ff.has_aload)
		return "it has an async load";
	if (ff.has_sr)
		return "it has a set/reset";
	return nullptr;
}

// Which of a register's stored values a fold is carrying. All three travel the
// same way, and differ only in where the operands' copies are read from.
enum class FoldKind { Init, Srst, Arst };

const char *fold_kind_name(FoldKind kind)
{
	switch (kind) {
	case FoldKind::Srst:
		return "sync reset";
	case FoldKind::Arst:
		return "async reset";
	default:
		return "init";
	}
}

// The value a data input of a chain cell contributes to a fold: a merged
// register's copy of it, or a constant operand, which holds its own value on
// every cycle, reset cycles and the first cycle alike. Only called once
// collect_merges has established that every input is one or the other.
Const operand_value(Module *module, SigMap &sigmap, FfInitVals &initvals, Cell *cell,
		IdString port, FoldKind kind)
{
	SigSpec in = sigmap(cell->getPort(port));
	if (in.is_fully_const())
		return in.as_const();
	IdString drv_port;
	Cell *drv = unique_driver(module, sigmap, in, drv_port);
	log_assert(drv && drv_port == ID::Q);
	FfData ff(&initvals, drv);
	switch (kind) {
	case FoldKind::Srst:
		return ff.val_srst;
	case FoldKind::Arst:
		return ff.val_arst;
	default:
		return ff.val_init;
	}
}

// A stored value has to reach the far side of the chain as the value that cycle
// would have produced there, so the pass evaluates the chain on constants. An
// init of 0 crossing a $not arrives as ~0; a reset value crosses the same way,
// because reset ? f(RSTVAL) : f(x) is f of reset ? RSTVAL : x, so it is enough
// for the register left behind to reset to f(RSTVAL). A merge folds the other
// operands' copies in alongside, which is why they all have to reset on the
// same cycles even though they need not reset to the same value.
//
// A $buf chain needs no arithmetic, being the identity, but the value still has
// to move onto the register's new Q net rather than stay on the old one, so it
// is not a special case here.
Const fold_value(Module *module, SigMap &sigmap, FfInitVals &initvals, Cell *flop,
		const std::vector<ChainStep> &chain, FoldKind kind, Const cur)
{
	for (auto &step : chain) {
		if (is_buf(step.cell))
			continue;

		std::vector<Const> args;
		for (auto port : data_inputs(step.cell))
			args.push_back(port == step.port ? cur
					: operand_value(module, sigmap, initvals, step.cell, port, kind));

		bool err = false;
		Const out;
		if (GetSize(args) == 3)
			out = CellTypes::eval(step.cell, args[0], args[1], args[2], &err);
		else if (GetSize(args) == 2)
			out = CellTypes::eval(step.cell, args[0], args[1], &err);
		else
			out = CellTypes::eval(step.cell, args[0], Const(), &err);
		if (err)
			log_cmd_error("Flop %s has a %s value that opt_retime cannot fold through "
					"cell %s, because it cannot evaluate %s on constants.\n",
					log_id(flop), fold_kind_name(kind), log_id(step.cell),
					log_id(step.cell->type));
		cur = out;
	}
	return cur;
}

// Fold one kind of stored value through the chain, if there is one to fold.
// Returns false when every copy of it is undefined, meaning there is nothing to
// carry. A mix of defined and undefined copies is refused rather than folded:
// evaluating one against the other gives undefined bits back, which would
// quietly discard what the defined side said.
bool fold_through(Module *module, SigMap &sigmap, FfInitVals &initvals, Cell *flop,
		const std::vector<ChainStep> &chain, FoldKind kind, Const start, Const &result)
{
	bool any = !start.is_fully_undef();
	bool all = start.is_fully_def();
	for (auto &step : chain) {
		if (is_buf(step.cell))
			continue;
		for (auto port : data_inputs(step.cell)) {
			if (port == step.port)
				continue;
			// A constant operand is not a stored value. It holds the same value
			// on every cycle, so it feeds a fold that is already happening but
			// never causes one, and it can never be the undefined half of a
			// mix. Counting it here would demand a stored value of every
			// register moving across a cell with a constant operand.
			if (sigmap(step.cell->getPort(port)).is_fully_const())
				continue;
			Const val = operand_value(module, sigmap, initvals, step.cell, port, kind);
			any = any || !val.is_fully_undef();
			all = all && val.is_fully_def();
		}
	}
	if (!any)
		return false;
	if (!all)
		log_cmd_error("Flop %s cannot move because the move would fold %s values together "
				"and only some of them are defined.\n", log_id(flop), fold_kind_name(kind));
	result = fold_value(module, sigmap, initvals, flop, chain, kind, start);
	return true;
}

const char *mismatch_reason(SigMap &sigmap, FfData &ref, FfData &ff)
{
	// Compared as a set of controls rather than by cell type, because the
	// single-bit cells spell their reset value into the type name and that
	// value is exactly what a fold is allowed to change: $_SDFF_PP0_ and
	// $_SDFF_PP1_ are the same kind of register for our purposes.
	if (ff.has_clk != ref.has_clk || ff.has_ce != ref.has_ce ||
			ff.has_srst != ref.has_srst || ff.has_arst != ref.has_arst ||
			ff.has_aload != ref.has_aload || ff.has_sr != ref.has_sr ||
			ff.is_fine != ref.is_fine)
		return "a different set of controls than";
	// The net and the polarity are reported separately throughout, because
	// they look nothing alike to someone reading a netlist. A different net
	// is visible in a picture; a polarity lives in a parameter and draws
	// identically, so saying only "a different enable" of two registers
	// sharing one enable net reads as a contradiction of what is on screen.
	if (!ff.has_clk)
		return "no clock to share with";
	if (sigmap(ff.sig_clk) != sigmap(ref.sig_clk))
		return "a different clock net than";
	if (ff.pol_clk != ref.pol_clk)
		return "a clock of the opposite edge to";
	// Enables must agree exactly across everything a move merges. One register
	// holding while another updates feeds the cut a mix of old and new inputs,
	// and the single register left behind has no way to reproduce that.
	if (ff.has_ce) {
		if (sigmap(ff.sig_ce) != sigmap(ref.sig_ce))
			return "a different enable net than";
		if (ff.pol_ce != ref.pol_ce)
			return "an enable of the opposite polarity to";
	}
	// Resets have to agree on when they fire, for the same reason enables do,
	// but deliberately not on what they load: the values are folded together
	// exactly as init values are, so two registers resetting to different
	// values on the same net merge into one resetting to f of both.
	if (ff.has_srst) {
		if (sigmap(ff.sig_srst) != sigmap(ref.sig_srst))
			return "a different sync reset net than";
		if (ff.pol_srst != ref.pol_srst)
			return "a sync reset of the opposite polarity to";
	}
	if (ff.has_arst) {
		if (sigmap(ff.sig_arst) != sigmap(ref.sig_arst))
			return "a different async reset net than";
		if (ff.pol_arst != ref.pol_arst)
			return "an async reset of the opposite polarity to";
	}
	// Widths are deliberately not compared: a $mux merges a 1-bit select
	// register with its wide data registers.
	return nullptr;
}

// A forward move across a multi-input cell folds every other data input into
// the register it leaves behind. The flop on that input is deleted only when
// nothing else reads it; extra readers keep the flop and the cut is rewired
// to its D, which is the same netlist as cloning a fanout-1 copy and merging
// that copy away.
std::vector<Merge> collect_merges(Module *module, SigMap &sigmap, FfInitVals &initvals,
		Cell *flop, FfData &ref, const std::vector<ChainStep> &chain)
{
	std::vector<Merge> merges;
	for (auto &step : chain) {
		for (auto port : data_inputs(step.cell)) {
			if (port == step.port)
				continue;

			SigSpec in = sigmap(step.cell->getPort(port));

			// A constant operand needs no register to merge, because it is
			// already time invariant: reg(c) is c on every cycle, so
			// f(reg(x), c) equals reg(f(x, c)) for the same reason it holds
			// when every input is registered. Nothing is folded away and
			// nothing is rewired, the cut goes on reading the constant where
			// it sits. A partly constant input still refuses below, since
			// unique_driver will not find a single flop behind it.
			if (in.is_fully_const())
				continue;

			IdString drv_port;
			Cell *drv = unique_driver(module, sigmap, in, drv_port);
			if (!drv || drv_port != ID::Q || !drv->is_builtin_ff())
				log_cmd_error("Input %s of cell %s is not driven by a flop or a constant, so "
						"flop %s cannot move forward across it.\n",
						log_id(port), log_id(step.cell), log_id(flop));

			FfData ff(&initvals, drv);
			// why carries its own preposition, so that a mismatched net and a
			// mismatched polarity can each be named for what they are.
			if (const char *why = mismatch_reason(sigmap, ref, ff))
				log_cmd_error("Flop %s on input %s of cell %s has %s flop %s.\n",
						log_id(drv), log_id(port), log_id(step.cell), why, log_id(flop));
			if (const char *why = unmovable_reason(ff))
				log_cmd_error("Flop %s on input %s of cell %s cannot be merged because %s.\n",
						log_id(drv), log_id(port), log_id(step.cell), why);

			IdString reader_port;
			Cell *reader = unique_reader(module, sigmap, sigmap(drv->getPort(ID::Q)), reader_port);
			bool keep = reader != step.cell || reader_port != port;

			merges.push_back({drv, step.cell, port, drv->getPort(ID::D), keep});
		}
	}
	return merges;
}

void check_controls(FfData &ff, SigMap &sigmap, const pool<SigBit> &forbidden)
{
	auto check = [&](const SigSpec &sig, const char *what) {
		if (bits_overlap(forbidden, sigmap(sig)))
			log_cmd_error("Flop %s control %s uses a data wire being retimed.\n", log_id(ff.cell), what);
	};
	if (ff.has_clk)
		check(ff.sig_clk, "CLK");
	if (ff.has_ce)
		check(ff.sig_ce, "EN");
	if (ff.has_arst)
		check(ff.sig_arst, "ARST");
	if (ff.has_srst)
		check(ff.sig_srst, "SRST");
	if (ff.has_aload)
		check(ff.sig_aload, "ALOAD");
	if (ff.has_sr) {
		check(ff.sig_set, "SET");
		check(ff.sig_clr, "CLR");
	}
}

void apply_move(Module *module, Cell *flop, Cell *cut)
{
	if (!flop->is_builtin_ff())
		log_cmd_error("Cell %s is not a built-in flip-flop.\n", log_id(flop));
	if (data_inputs(cut).empty())
		log_cmd_error("Cut cell %s has type %s, which opt_retime cannot move across yet.\n",
				log_id(cut), log_id(cut->type));
	if (flop == cut)
		log_cmd_error("Flop and cut must be different cells.\n");

	SigMap sigmap(module);
	FfInitVals initvals(&sigmap, module);

	FfData ff(&initvals, flop);
	if (!ff.has_clk || !flop->hasPort(ID::D) || !flop->hasPort(ID::Q))
		log_cmd_error("Cell %s is not a clocked flop with D and Q.\n", log_id(flop));

	std::vector<ChainStep> chain = collect_chain(module, sigmap, flop, cut);

	// The chain walk only follows a port when it carries the whole signal, so
	// every register on the path already matches the width of the port it
	// drives. What is left to check is the register the move leaves behind,
	// which takes the width of the cut output.
	for (auto &step : chain)
		if (!step.cell->hasPort(ID::Y))
			log_cmd_error("Cell %s is missing port Y.\n", log_id(step.cell));

	// Every cell on the chain except a $buf transforms the values the register
	// loads, and the ones left in unmovable_reason arrive on a net rather than
	// as a constant, so there is nothing to fold and the move is refused. A
	// $buf passes them through untouched and needs no such check.
	for (auto &step : chain)
		if (!is_buf(step.cell))
			if (const char *why = unmovable_reason(ff))
				log_cmd_error("Flop %s cannot move across cell %s because %s, which the move "
						"would have to push through the cell.\n",
						log_id(flop), log_id(step.cell), why);

	ChainStep first_step = chain.front();
	Cell *first = first_step.cell;
	Cell *last = chain.back().cell;

	SigSpec d = flop->getPort(ID::D);
	SigSpec q = flop->getPort(ID::Q);
	SigSpec y = last->getPort(ID::Y);

	SigSpec map_q = sigmap(q);
	SigSpec map_y = sigmap(y);
	SigSpec map_d = sigmap(d);

	std::vector<CellPort> q_readers;
	bool q_partial = false, q_output = false;
	scan_readers(module, sigmap, map_q, q_readers, q_partial, q_output);
	bool peel = q_partial || q_output;
	if (!peel) {
		for (auto &reader : q_readers)
			if (reader.cell != first || reader.port != first_step.port)
				peel = true;
	}

	// A leftover copy keeps the original D. If that D sits on the after-path
	// of the cut, rewriting the cut would change the copy's input, so the
	// extra readers would not keep seeing the original register. Checked
	// before merges so a loop with an observe tap fails for that reason
	// rather than whatever the other operand happens to look like.
	if (peel && signal_reaches(module, sigmap, map_y, map_d))
		log_cmd_error("Flop %s cannot move across %s: other readers need a copy left "
				"behind, but the flop's D depends on the cut, so that copy would "
				"not keep its original input.\n",
				log_id(flop), log_id(cut));

	std::vector<Merge> merges = collect_merges(module, sigmap, initvals, flop, ff, chain);

	// Every stored value the register carries is folded through the chain
	// before anything is rewired, while the merged registers are still around
	// to read their copies from.
	Const init_folded, srst_folded, arst_folded;
	bool got_init = fold_through(module, sigmap, initvals, flop, chain,
			FoldKind::Init, ff.val_init, init_folded);
	bool got_srst = ff.has_srst && fold_through(module, sigmap, initvals, flop, chain,
			FoldKind::Srst, ff.val_srst, srst_folded);
	bool got_arst = ff.has_arst && fold_through(module, sigmap, initvals, flop, chain,
			FoldKind::Arst, ff.val_arst, arst_folded);

	// TODO relax some of these contraints by rewiring these control nets
	pool<SigBit> forbidden = wire_bits(map_y);
	if (!peel)
		for (auto bit : wire_bits(map_q))
			forbidden.insert(bit);
	for (auto &merge : merges) {
		if (merge.keep)
			continue;
		for (auto bit : wire_bits(sigmap(merge.flop->getPort(ID::Q))))
			forbidden.insert(bit);
	}

	// TODO relax control checks
	check_controls(ff, sigmap, forbidden);

	if (peel) {
		IdString left_name = module->uniquify(flop->name.str() + "_fanout");
		module->addCell(left_name, flop);
		flop->unsetPort(ID::Q);
		log("Leaving a copy of flop %s as %s for its other readers.\n",
				log_id(flop), log_id(left_name));
	}

	// The register keeps its name, so the caller can still find the flop it
	// named, but it takes the width of the cut output. Where that width is
	// unchanged the old Q net is reused as the link from the cut to the
	// register, which is what the pass has always done for $buf chains.
	// A leftover copy already owns that net, so a peeled move always gets a
	// fresh link.
	SigSpec link = q;
	if (GetSize(y) != GetSize(q)) {
		if (ff.is_fine)
			log_cmd_error("Flop %s is a single-bit cell and cannot widen to %d bits.\n",
					log_id(flop), GetSize(y));
		log("Resizing flop %s from %d to %d bits.\n", log_id(flop), GetSize(q), GetSize(y));
		link = module->addWire(module->uniquify(flop->name.str() + "_retimed"), GetSize(y));
	} else if (peel) {
		link = module->addWire(module->uniquify(flop->name.str() + "_retimed"), GetSize(y));
	}
	first->setPort(first_step.port, d);
	last->setPort(ID::Y, link);

	// The old Q net has become the combinational link from the cut, and the
	// merged registers that are about to go give up their init values: one
	// left behind on either would be read as a register's first-cycle value
	// by everything downstream. A leftover copy still drives the old Q net,
	// and a kept merge still drives its Q, so those inits stay.
	if (!peel)
		ff.remove_init();
	for (auto &merge : merges)
		if (!merge.keep)
			initvals.remove_init(sigmap(merge.flop->getPort(ID::Q)));

	// Merged flops with no other readers disappear into the one flop the
	// move leaves behind. Extra readers keep their flop; only the cut is
	// rewired to D.
	int kept = 0;
	for (auto &merge : merges) {
		merge.cell->setPort(merge.port, merge.sig_d);
		if (merge.keep) {
			kept++;
			continue;
		}
		module->remove(merge.flop);
	}

	// The register is rebuilt rather than rewired, because a folded reset value
	// can change which cell it has to be: the single-bit types spell the value
	// they reset to into their name, so a $_SDFF_PP0_ whose fold inverts that
	// value has to come back as a $_SDFF_PP1_. Emitting from FfData picks the
	// type from the values, resizes the parameters, and writes the init value
	// onto the new Q net on the way. Undefined values still have to be resized,
	// or emitting a widened register would assert on their width.
	IdString flop_name = ff.name;
	ff.sig_d = link;
	ff.sig_q = y;
	ff.width = GetSize(y);
	ff.val_init = got_init ? init_folded : Const(State::Sx, GetSize(y));
	if (ff.has_srst)
		ff.val_srst = got_srst ? srst_folded : Const(State::Sx, GetSize(y));
	if (ff.has_arst)
		ff.val_arst = got_arst ? arst_folded : Const(State::Sx, GetSize(y));
	if (!ff.emit())
		log_cmd_error("Flop %s did not survive being rebuilt after the move.\n",
				log_id(flop_name));

	if (got_init)
		log("Folded init value of flop %s to %s.\n", log_id(flop_name), log_signal(init_folded));
	if (got_srst)
		log("Folded sync reset value of flop %s to %s.\n", log_id(flop_name),
				log_signal(srst_folded));
	if (got_arst)
		log("Folded async reset value of flop %s to %s.\n", log_id(flop_name),
				log_signal(arst_folded));

	log("Retimed %s forward across %d cell(s) ending at %s, merging %d flop(s).\n",
			log_id(flop_name), GetSize(chain), log_id(cut), GetSize(merges));
	if (kept)
		log("Kept %d merged flop(s) that still have other readers.\n", kept);
}

struct OptRetimePass : public Pass {
	OptRetimePass() : Pass("opt_retime", "retime sequential circuits") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_retime -flop <cell> -cut <cell> -forward [selection]\n");
		log("\n");
		log("This pass retimes one register forward across a chain of combinational\n");
		log("cells. Only forward moves are supported: -backward is rejected.\n");
		log("\n");
		log("    -flop <cell>\n");
		log("        register to move.\n");
		log("\n");
		log("    -cut <cell>\n");
		log("        cell on the after-path of the register. May be one or more\n");
		log("        cells away; every cell between the flop and the cut moves with\n");
		log("        it. After the flop, the path must be a unique chain. Supported\n");
		log("        cut types are $buf, $mux, $not, $add, $sub, $and, $or, $xor,\n");
		log("        $xnor, $shl, $shr, the comparators ($eq, $ne, $lt, $le, $gt,\n");
		log("        $ge) and the $reduce_* cells. Every input of the cut counts\n");
		log("        as a data input, the $mux select and a shift amount included,\n");
		log("        so all of them have to be registered or constant.\n");
		log("\n");
		log("    -forward\n");
		log("        move the register downstream, past -cut. Required. Where the\n");
		log("        path runs through a cell with several data inputs, the\n");
		log("        registers on the other inputs are merged into the moved\n");
		log("        register, so they must share its clock, its enable and the\n");
		log("        net it resets on. If those registers are read elsewhere\n");
		log("        they stay, and only the cut is rewired to their D. The\n");
		log("        moved register keeps its name but takes the width of the cut\n");
		log("        output, so a move across a reduction narrows it, and a move\n");
		log("        across an adder that keeps its carry, or one entered on a\n");
		log("        $mux select, widens it.\n");
		log("\n");
		log("        A clock enable moves along with the register untouched,\n");
		log("        since holding a value commutes with a pure function. Init\n");
		log("        and reset values are folded instead: they are evaluated\n");
		log("        through the chain so the register left behind starts at, and\n");
		log("        resets to, what the cut would have made of the old value.\n");
		log("        Merged registers need not reset to the same value, but they\n");
		log("        do have to reset on the same net, and every value being\n");
		log("        folded has to be defined. An async load or a set/reset\n");
		log("        arrives on a net rather than as a constant, so there is\n");
		log("        nothing to fold and the move is refused.\n");
		log("\n");
		log("        A register read by more than one cell is copied: the named\n");
		log("        flop moves, and a leftover copy keeps the original Q for\n");
		log("        the other readers. Combinational fanout on the path is\n");
		log("        still refused, as is a leftover copy whose D depends on\n");
		log("        the cut (a register on a loop with an observe tap).\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_RETIME pass.\n");

		std::string flop, cut_cell;
		bool forward = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-flop" && argidx + 1 < args.size()) {
				flop = args[++argidx];
				continue;
			}
			if (args[argidx] == "-cut" && argidx + 1 < args.size()) {
				cut_cell = args[++argidx];
				continue;
			}
			if (args[argidx] == "-forward") {
				forward = true;
				continue;
			}
			// Backward retiming was dropped: a backward move has to split the
			// register onto every data input of the cut, which is a different
			// transform than the merge a forward move does. Reject it here
			// rather than silently doing something else.
			if (args[argidx] == "-backward")
				log_cmd_error("Backward moves are not supported, opt_retime only moves "
						"registers forward.\n");
			break;
		}
		extra_args(args, argidx, design);

		if (flop.empty())
			log_cmd_error("Missing required -flop <cell> option.\n");
		if (cut_cell.empty())
			log_cmd_error("Missing required -cut <cell> option.\n");
		if (!forward)
			log_cmd_error("Missing required -forward option.\n");

		Module *module = nullptr;
		Cell *flop_cell = nullptr;
		Cell *cut = nullptr;
		for (auto mod : design->selected_modules()) {
			Cell *found = mod->cell(RTLIL::escape_id(flop));
			if (!found)
				continue;
			if (module)
				log_cmd_error("Flop cell '%s' found in more than one selected module.\n", flop.c_str());
			module = mod;
			flop_cell = found;
			cut = mod->cell(RTLIL::escape_id(cut_cell));
		}
		if (!flop_cell)
			log_cmd_error("Flop cell '%s' not found in the selection.\n", flop.c_str());
		if (!cut)
			log_cmd_error("Cut cell '%s' not found in module %s.\n", cut_cell.c_str(), log_id(module));

		log("Move: module=%s flop=%s direction=forward cut=%s\n",
				log_id(module), log_id(flop_cell), log_id(cut));

		apply_move(module, flop_cell, cut);
	}
} OptRetimePass;

PRIVATE_NAMESPACE_END
