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

static std::vector<Cell *> collect_buf_chain(Module *module, SigMap &sigmap, Cell *flop, Cell *cut, bool forward)
{
	std::vector<Cell *> chain;
	pool<Cell *> seen;
	SigSpec cur = sigmap(forward ? flop->getPort(ID::Q) : flop->getPort(ID::D));

	while (true) {
		IdString port;

		// Generalize to beyond single-fanout
		Cell *next = forward ? unique_reader(module, sigmap, cur, port)
				     : unique_driver(module, sigmap, cur, port);
		IdString need_port = forward ? ID::A : ID::Y;
		if (!next || port != need_port || !is_buf(next))
			break;
		if (seen.count(next))
			log_cmd_error("Cycle on the %s-path of flop %s.\n",
					forward ? "after" : "before", log_id(flop));
		seen.insert(next);
		chain.push_back(next);
		if (next == cut)
			break;
		cur = sigmap(next->getPort(forward ? ID::Y : ID::A));
	}

	if (chain.empty() || chain.back() != cut)
		log_cmd_error("Cut %s is not on the %s-path of flop %s.\n",
				log_id(cut), forward ? "after" : "before", log_id(flop));
	return chain;
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

static void apply_buf_move(Module *module, Cell *flop, Cell *cut, bool forward)
{
	if (!flop->is_builtin_ff())
		log_cmd_error("Cell %s is not a built-in flip-flop.\n", log_id(flop));
	if (!is_buf(cut))
		log_cmd_error("Cut cell %s is not a $buf (only buffer cuts are supported).\n", log_id(cut));
	if (flop == cut)
		log_cmd_error("Flop and cut must be different cells.\n");

	FfData ff(nullptr, flop);
	if (!ff.has_clk || !flop->hasPort(ID::D) || !flop->hasPort(ID::Q))
		log_cmd_error("Cell %s is not a clocked flop with D and Q.\n", log_id(flop));
	if (!cut->hasPort(ID::A) || !cut->hasPort(ID::Y))
		log_cmd_error("Cut cell %s is missing A/Y ports.\n", log_id(cut));

	SigMap sigmap(module);
	// TODO: Generalize to beyond just $buf cells
	std::vector<Cell *> chain = collect_buf_chain(module, sigmap, flop, cut, forward);

	Cell *first = forward ? chain.front() : chain.back();
	Cell *last = forward ? chain.back() : chain.front();

	SigSpec d = flop->getPort(ID::D);
	SigSpec q = flop->getPort(ID::Q);
	SigSpec a = first->getPort(ID::A);
	SigSpec y = last->getPort(ID::Y);

	// TODO Generalize to support bit-width differences
	if (GetSize(d) != GetSize(q) || GetSize(a) != GetSize(y) || GetSize(q) != GetSize(a))
		log_cmd_error("Width mismatch between flop %s and cut %s.\n", log_id(flop), log_id(cut));

	SigSpec map_q = sigmap(q);
	SigSpec map_y = sigmap(y);

	// TODO relax some of these contraints by rewiring these control nets
	pool<SigBit> forbidden = wire_bits(map_q);
	for (auto bit : wire_bits(map_y))
		forbidden.insert(bit);

	// TODO relax control checks
	check_controls(ff, sigmap, forbidden);

	if (forward) {
		first->setPort(ID::A, d);
		flop->setPort(ID::Q, y);
		last->setPort(ID::Y, q);
		flop->setPort(ID::D, q);
	} else {
		flop->setPort(ID::D, a);
		flop->setPort(ID::Q, y);
		first->setPort(ID::A, y);
		last->setPort(ID::Y, q);
	}

	log("Retimed %s %s across %d $buf cell(s) ending at %s.\n",
			log_id(flop), forward ? "forward" : "backward", GetSize(chain), log_id(cut));
}

struct OptRetimePass : public Pass {
	OptRetimePass() : Pass("opt_retime", "retime sequential circuits") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_retime -flop <cell> -cut <cell> -forward|-backward [selection]\n");
		log("\n");
		log("This pass retimes one register across a chain of $buf cells.\n");
		log("\n");
		log("    -flop <cell>\n");
		log("        register to move.\n");
		log("\n");
		log("    -cut <cell>\n");
		log("        $buf on the after-path (forward) or before-path (backward).\n");
		log("        May be one or more cells away; every $buf between the flop\n");
		log("        and the cut moves with it. The path must be a unique chain.\n");
		log("\n");
		log("    -forward\n");
		log("        move the register downstream, past -cut.\n");
		log("\n");
		log("    -backward\n");
		log("        move the register upstream, past -cut.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_RETIME pass.\n");

		std::string flop, cut_cell;
		bool forward = false, backward = false;

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
			if (args[argidx] == "-backward") {
				backward = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (flop.empty())
			log_cmd_error("Missing required -flop <cell> option.\n");
		if (cut_cell.empty())
			log_cmd_error("Missing required -cut <cell> option.\n");
		if (forward == backward)
			log_cmd_error("Must specify exactly one of -forward or -backward.\n");

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

		log("Move: module=%s flop=%s direction=%s cut=%s\n",
				log_id(module), log_id(flop_cell), forward ? "forward" : "backward", log_id(cut));
		
	 // TODO: Generalize to beyong just $buf cells
		apply_buf_move(module, flop_cell, cut, forward);
	}
} OptRetimePass;

PRIVATE_NAMESPACE_END
