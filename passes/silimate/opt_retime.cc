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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static bool is_buf(Cell *cell)
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
// TODO: the shifts need their amount port merged the way $mux merges S.
static std::vector<IdString> data_inputs(Cell *cell)
{
	if (is_buf(cell))
		return {ID::A};
	if (cell->type.in(ID($add), ID($sub), ID($and), ID($or), ID($xor), ID($xnor),
			ID($eq), ID($ne), ID($lt), ID($le), ID($gt), ID($ge)))
		return {ID::A, ID::B};
	if (cell->type.in(ID($not), ID($reduce_and), ID($reduce_or), ID($reduce_xor),
			ID($reduce_xnor), ID($reduce_bool)))
		return {ID::A};
	if (cell->type == ID($mux))
		return {ID::A, ID::B, ID::S};
	return {};
}

static bool is_data_input(Cell *cell, IdString port)
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
// single register the move leaves behind.
struct Merge {
	Cell *flop;
	Cell *cell;
	IdString port;
	SigSpec sig_d;
};

static pool<SigBit> wire_bits(const SigSpec &sig)
{
	pool<SigBit> bits;
	for (auto bit : sig) {
		if (!bit.is_wire())
			log_cmd_error("Retiming signal %s contains a constant bit.\n", log_signal(sig));
		bits.insert(bit);
	}
	return bits;
}

static bool bits_overlap(const pool<SigBit> &bits, const SigSpec &sig)
{
	for (auto bit : sig)
		if (bit.is_wire() && bits.count(bit))
			return true;
	return false;
}

static Cell *unique_reader(Module *module, SigMap &sigmap, const SigSpec &sig, IdString &port)
{
	pool<SigBit> bits = wire_bits(sig);
	Cell *found = nullptr;
	port = IdString();

	for (auto cell : module->cells()) {
		for (auto &conn : cell->connections()) {
			if (!cell->input(conn.first))
				continue;
			for (auto bit : sigmap(conn.second)) {
				if (!bits.count(bit))
					continue;
				if (found && (cell != found || conn.first != port))
					return nullptr;
				found = cell;
				port = conn.first;
			}
		}
	}
	for (auto wire : module->wires()) {
		if (!wire->port_output)
			continue;
		for (auto bit : sigmap(SigSpec(wire)))
			if (bits.count(bit))
				return nullptr;
	}
	if (!found || sigmap(found->getPort(port)) != sig)
		return nullptr;
	return found;
}

static Cell *unique_driver(Module *module, SigMap &sigmap, const SigSpec &sig, IdString &port)
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

static std::vector<ChainStep> collect_chain(Module *module, SigMap &sigmap, Cell *flop, Cell *cut)
{
	std::vector<ChainStep> chain;
	pool<Cell *> seen;
	SigSpec cur = sigmap(flop->getPort(ID::Q));

	while (true) {
		IdString port;

		// Generalize to beyond single-fanout
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

	if (chain.empty() || chain.back().cell != cut)
		log_cmd_error("Cut %s is not on the after-path of flop %s.\n", log_id(cut), log_id(flop));
	return chain;
}

// A move relocates the register's stored value across the chain, so it only
// holds if the value survives the trip. That is free for a $buf, which is the
// identity, but any other cell transforms it: moving an init value of 0 across
// a $not would have to store ~0 instead. The same goes for a merged register,
// whose value is folded through the cut along with everything else.
// TODO: support enables, resets and init values by pushing their values through
// the chain rather than refusing.
static const char *unmovable_reason(FfData &ff)
{
	if (ff.has_ce || ff.has_aload || ff.has_sr)
		return "it has an enable";
	if (ff.has_arst || ff.has_srst)
		return "it has a reset";
	if (!ff.val_init.is_fully_undef())
		return "it has an init value";
	return nullptr;
}

static const char *mismatch_reason(SigMap &sigmap, FfData &ref, FfData &ff)
{
	if (ff.cell->type != ref.cell->type)
		return "a different cell type";
	if (!ff.has_clk || ff.pol_clk != ref.pol_clk || sigmap(ff.sig_clk) != sigmap(ref.sig_clk))
		return "a different clock";
	// Widths are deliberately not compared: a $mux merges a 1-bit select
	// register with its wide data registers.
	return nullptr;
}

// A forward move across a multi-input cell only removes a register if every
// other data input is fed by an equivalent register that nothing else reads.
static std::vector<Merge> collect_merges(Module *module, SigMap &sigmap, FfInitVals &initvals,
		Cell *flop, FfData &ref, const std::vector<ChainStep> &chain)
{
	std::vector<Merge> merges;
	for (auto &step : chain) {
		for (auto port : data_inputs(step.cell)) {
			if (port == step.port)
				continue;

			IdString drv_port;
			Cell *drv = unique_driver(module, sigmap, sigmap(step.cell->getPort(port)), drv_port);
			if (!drv || drv_port != ID::Q || !drv->is_builtin_ff())
				log_cmd_error("Input %s of cell %s is not driven by a flop, so flop %s cannot "
						"move forward across it.\n",
						log_id(port), log_id(step.cell), log_id(flop));

			FfData ff(&initvals, drv);
			if (const char *why = mismatch_reason(sigmap, ref, ff))
				log_cmd_error("Flop %s on input %s of cell %s has %s than flop %s.\n",
						log_id(drv), log_id(port), log_id(step.cell), why, log_id(flop));
			if (const char *why = unmovable_reason(ff))
				log_cmd_error("Flop %s on input %s of cell %s cannot be merged because %s.\n",
						log_id(drv), log_id(port), log_id(step.cell), why);

			IdString reader_port;
			Cell *reader = unique_reader(module, sigmap, sigmap(drv->getPort(ID::Q)), reader_port);
			if (reader != step.cell || reader_port != port)
				log_cmd_error("Flop %s on input %s of cell %s has other readers, so it cannot "
						"be merged away.\n",
						log_id(drv), log_id(port), log_id(step.cell));

			merges.push_back({drv, step.cell, port, drv->getPort(ID::D)});
		}
	}
	return merges;
}

static void check_controls(FfData &ff, SigMap &sigmap, const pool<SigBit> &forbidden)
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

static void apply_move(Module *module, Cell *flop, Cell *cut)
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

	// Every cell on the chain except a $buf transforms the value the register
	// holds, so the register must not be holding one. This covers both the
	// multi-input cells, whose merges fold several stored values together, and
	// the single-input ones like $not, where nothing merges and the width may
	// not even change, but the stored value is still wrong on the far side.
	for (auto &step : chain)
		if (!is_buf(step.cell))
			if (const char *why = unmovable_reason(ff))
				log_cmd_error("Flop %s cannot move across cell %s because %s, which the move "
						"would have to push through the cell.\n",
						log_id(flop), log_id(step.cell), why);

	std::vector<Merge> merges = collect_merges(module, sigmap, initvals, flop, ff, chain);

	ChainStep first_step = chain.front();
	Cell *first = first_step.cell;
	Cell *last = chain.back().cell;

	SigSpec d = flop->getPort(ID::D);
	SigSpec q = flop->getPort(ID::Q);
	SigSpec y = last->getPort(ID::Y);

	SigSpec map_q = sigmap(q);
	SigSpec map_y = sigmap(y);

	// TODO relax some of these contraints by rewiring these control nets
	pool<SigBit> forbidden = wire_bits(map_q);
	for (auto bit : wire_bits(map_y))
		forbidden.insert(bit);
	for (auto &merge : merges)
		for (auto bit : wire_bits(sigmap(merge.flop->getPort(ID::Q))))
			forbidden.insert(bit);

	// TODO relax control checks
	check_controls(ff, sigmap, forbidden);

	// The register keeps its cell, so the caller can still find the flop it
	// named, but it takes the width of the cut output. Where that width is
	// unchanged the old Q net is reused as the link from the cut to the
	// register, which is what the pass has always done for $buf chains.
	SigSpec link = q;
	if (GetSize(y) != GetSize(q)) {
		// A register holding a value has already been refused above: only a
		// non-$buf chain can change the width, and that is exactly the case
		// that check covers. What is left is the mechanics of resizing.
		if (ff.is_fine)
			log_cmd_error("Flop %s is a single-bit cell and cannot widen to %d bits.\n",
					log_id(flop), GetSize(y));
		if (!flop->hasParam(ID::WIDTH))
			log_cmd_error("Flop %s has no WIDTH parameter to resize.\n", log_id(flop));
		log("Resizing flop %s from %d to %d bits.\n", log_id(flop), GetSize(q), GetSize(y));
		link = module->addWire(module->uniquify(flop->name.str() + "_retimed"), GetSize(y));
		flop->setParam(ID::WIDTH, GetSize(y));
	}
	first->setPort(first_step.port, d);
	flop->setPort(ID::Q, y);
	last->setPort(ID::Y, link);
	flop->setPort(ID::D, link);

	// The merged flops disappear into the one flop the move leaves behind.
	for (auto &merge : merges) {
		merge.cell->setPort(merge.port, merge.sig_d);
		module->remove(merge.flop);
	}

	log("Retimed %s forward across %d cell(s) ending at %s, merging %d flop(s).\n",
			log_id(flop), GetSize(chain), log_id(cut), GetSize(merges));
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
		log("        it. The path must be a unique chain. Supported cut types are\n");
		log("        $buf, $mux, $not, $add, $sub, $and, $or, $xor, $xnor, the\n");
		log("        comparators ($eq, $ne, $lt, $le, $gt, $ge) and the\n");
		log("        $reduce_* cells. Every input of the cut counts as a data\n");
		log("        input, the $mux select included, so all of them have to be\n");
		log("        registered.\n");
		log("\n");
		log("    -forward\n");
		log("        move the register downstream, past -cut. Required. Where the\n");
		log("        path runs through a cell with several data inputs, the\n");
		log("        registers on the other inputs are merged into the moved\n");
		log("        register, so they must share its clock and must not be read\n");
		log("        anywhere else. The moved register keeps its cell but takes the\n");
		log("        width of the cut output, so a move across a reduction narrows\n");
		log("        it, and a move across an adder that keeps its carry, or one\n");
		log("        entered on a $mux select, widens it.\n");
		log("\n");
		log("        A $buf is the identity, so it passes the register's stored\n");
		log("        value through untouched. Every other cut transforms it, and\n");
		log("        the pass cannot yet recompute it, so moving across one needs a\n");
		log("        plain clocked register with no enable, reset or init value.\n");
		log("\n");
		log("A register read by more than one cell blocks the path walk. Run\n");
		log("splitfanout on it first to get a fanout-1 copy to move.\n");
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
