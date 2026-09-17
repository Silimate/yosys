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

// A move the pass will not make, carrying the explanation the user sees.
//
// Thrown rather than logged so a refused move is an answer rather than the
// end of the script. try_move hands the reason back; the command wrapper
// reports it and leaves the design as it was.
//
// Every refusal is raised before the module is touched, so a refused move
// leaves the design exactly as it found it. That is a property of where the
// checks sit rather than of any rollback: nothing here can undo a half-applied
// move, which is why the failures that can only be noticed mid-rewrite are
// log_error instead. See the note above the emit calls.
struct MoveRefused {
	std::string reason;
};

// Takes its arguments the way log_cmd_error does, so a call reads the same
// after the rename and the format string is still checked against them.
template <typename... Args>
[[noreturn]] void refuse(FmtString<TypeIdentity<Args>...> fmt, const Args &... args)
{
	throw MoveRefused{fmt.format(args...)};
}

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
// The list is also the argument order fold_value hands to CellTypes::eval, so a
// type whose eval reads its operands in a different order has to be listed in
// that order rather than alphabetically: $bmux and $demux index with S where
// the arithmetic cells take a second operand, and are listed {A, S} for that
// reason. $slice reads its OFFSET off the cell, so its one data input is A.
//
// Gate-level $_AND_/$_NOR_/$_AOI* cells are not listed: this pass retimes
// word-level IR, before splitcells.
std::vector<IdString> data_inputs(Cell *cell)
{
	if (cell->type.in(ID($buf), ID($_BUF_)))
		return {ID::A};
	if (cell->type.in(ID($not), ID($neg), ID($pos), ID($logic_not), ID($slice),
			ID($reduce_and), ID($reduce_or), ID($reduce_xor),
			ID($reduce_xnor), ID($reduce_bool)))
		return {ID::A};
	if (cell->type.in(ID($add), ID($sub), ID($mul), ID($div), ID($mod),
			ID($divfloor), ID($modfloor), ID($pow), ID($and), ID($or),
			ID($xor), ID($xnor), ID($logic_and), ID($logic_or), ID($eq),
			ID($ne), ID($eqx), ID($nex), ID($lt), ID($le), ID($gt), ID($ge),
			ID($shl), ID($sshl), ID($shr), ID($sshr), ID($shift),
			ID($shiftx), ID($concat)))
		return {ID::A, ID::B};
	if (cell->type.in(ID($bmux), ID($demux)))
		return {ID::A, ID::S};
	// $pmux is here on the same terms as $mux: its whole packed B, one arm per
	// select bit, has to be registered alongside the select. Registering only
	// the arm the select picks would be a smaller move, and is not one the
	// pass makes for $mux either.
	if (cell->type.in(ID($mux), ID($bwmux), ID($pmux)))
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

// Output-bit driver, including the offset in that port. A 1-bit flop driving
// one slice of a wide $add.A is a different BitSrc per bit; unique_driver
// would reject the port because it is not one cell's full Q.
struct BitSrc {
	Cell *cell;
	IdString port;
	int offset;
};

// One bit of a data port the walk is crossing. Path bits are the after-path
// (the named flop's Q, or a previous cell's Y). Everything else on that port
// has to be a sibling flop on the same clock, or a constant: that is what
// makes f(reg(x), reg(y)) a legal forward move when x and y were bit-blasted
// into separate WIDTH=1 registers instead of one wide flop.
struct PortBit {
	enum Kind { Path, Flop, Const } kind;
	int path_offset;
	Cell *flop;
	int q_offset;
	State st;
};

// Which of a register's stored values a fold is carrying. All three travel the
// same way, and differ only in where the operands' copies are read from.
enum class FoldKind { Init, Srst, Arst, Aload };

const char *unmovable_reason(FfData &ff);
const char *mismatch_reason(SigMap &sigmap, FfData &ref, FfData &ff);
bool describe_port(SigMap &sigmap, const dict<SigBit, BitSrc> &drivers,
		FfInitVals &initvals, FfData &ref, Cell *named,
		Cell *cell, IdString port, const SigSpec &path_sig,
		std::vector<PortBit> &desc, bool error);
Cell *next_on_path(Module *module, SigMap &sigmap, const dict<SigBit, BitSrc> &drivers,
		FfInitVals &initvals, FfData &ref, Cell *named, const SigSpec &cur,
		IdString &port);

pool<SigBit> wire_bits(const SigSpec &sig)
{
	pool<SigBit> bits;
	for (auto bit : sig) {
		if (!bit.is_wire())
			refuse("Retiming signal %s contains a constant bit.\n", log_signal(sig));
		bits.insert(bit);
	}
	return bits;
}

// Add the wire bits of sig, passing over constants rather than refusing the way
// wire_bits does. Every caller is building the set of data nets a control signal
// may not also be, and a constant is not a net, so it cannot collide with one.
// That is what lets a cloned operand carry constant bits alongside its wires.
void insert_wire_bits(pool<SigBit> &bits, const SigSpec &sig)
{
	for (auto bit : sig)
		if (bit.is_wire())
			bits.insert(bit);
}

dict<SigBit, BitSrc> index_output_bits(Module *module, SigMap &sigmap)
{
	dict<SigBit, BitSrc> drivers;
	for (auto cell : module->cells()) {
		for (auto &conn : cell->connections()) {
			if (!cell->output(conn.first))
				continue;
			SigSpec mapped = sigmap(conn.second);
			for (int i = 0; i < GetSize(mapped); i++)
				if (mapped[i].is_wire())
					drivers[mapped[i]] = {cell, conn.first, i};
		}
	}
	return drivers;
}

// Does sig carry any bit of `bits`? A constant bit never matches, `bits`
// coming from wire_bits and so holding only wires.
bool touches(SigMap &sigmap, const pool<SigBit> &bits, const SigSpec &sig)
{
	for (auto bit : sigmap(sig))
		if (bits.count(bit))
			return true;
	return false;
}

// A module output has no port to point elsewhere, so every query below reports
// it separately from the cell ports.
bool output_touches(Module *module, SigMap &sigmap, const pool<SigBit> &bits)
{
	for (auto wire : module->wires())
		if (wire->port_output && touches(sigmap, bits, SigSpec(wire)))
			return true;
	return false;
}

// Readers of sig other than except.except_port. A cell reading only some bits
// counts, since a duplicate has to serve it bit for bit, so this is a list of
// ports rather than the full/partial split scan_readers makes. Module outputs
// are reported on their own. stop_early quits as soon as one port is known,
// for callers that only want the yes or no and would rather not walk the whole
// module to get it.
void scan_extra_readers(Module *module, SigMap &sigmap, const SigSpec &sig,
		Cell *except, IdString except_port,
		std::vector<CellPort> &readers, bool &output, bool stop_early = false)
{
	pool<SigBit> bits = wire_bits(sig);
	readers.clear();
	output = false;

	for (auto cell : module->cells()) {
		for (auto &conn : cell->connections()) {
			if (!cell->input(conn.first))
				continue;
			if (cell == except && conn.first == except_port)
				continue;
			if (touches(sigmap, bits, conn.second))
				readers.push_back({cell, conn.first});
			if (stop_early && !readers.empty())
				return;
		}
	}
	output = output_touches(module, sigmap, bits);
}

// True when something other than except.except_port reads any bit of sig.
// Partial reads count: a 1-bit Q sliced into a 33-bit $mul.A is a reader, and
// that is the case a leftover copy has to be left behind for.
bool has_other_readers(Module *module, SigMap &sigmap, const SigSpec &sig,
		Cell *except, IdString except_port)
{
	std::vector<CellPort> readers;
	bool output = false;
	scan_extra_readers(module, sigmap, sig, except, except_port, readers, output, true);
	return !readers.empty() || output;
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
			if (!touches(sigmap, bits, conn.second))
				continue;
			if (sigmap(conn.second) == sig)
				full.push_back({cell, conn.first});
			else
				partial = true;
		}
	}
	output = output_touches(module, sigmap, bits);
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
bool reaches_cut(Module *module, SigMap &sigmap, const dict<SigBit, BitSrc> &drivers,
		FfInitVals &initvals, FfData &ref, Cell *named, Cell *start, Cell *cut)
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
		Cell *next = next_on_path(module, sigmap, drivers, initvals, ref, named, cur, port);
		if (!next)
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

// One bit of a data port that is not on the after-path: either a constant, or
// a sibling flop the move can merge. Appends to desc and returns true, or says
// why not. error is set when the port belongs to -cut, where a bad sibling is
// a refusal; walking a candidate hop wants a quiet false instead, a bad port
// there being simply not a hop.
bool classify_off_path_bit(SigMap &sigmap, const dict<SigBit, BitSrc> &drivers,
		FfInitVals &initvals, FfData &ref, Cell *named,
		Cell *cell, IdString port, SigBit bit,
		std::vector<PortBit> &desc, bool error)
{
	if (!bit.is_wire()) {
		desc.push_back({PortBit::Const, 0, nullptr, 0, bit.data});
		return true;
	}

	auto it = drivers.find(bit);
	if (it == drivers.end() || it->second.port != ID::Q ||
			!it->second.cell->is_builtin_ff()) {
		if (error)
			refuse("Input %s of cell %s is not driven by a flop or a constant, so "
					"flop %s cannot move forward across it.\n",
					log_id(port), log_id(cell), log_id(named));
		return false;
	}

	Cell *drv = it->second.cell;
	// A named-flop Q bit off the path is a split of the register across this
	// port and somewhere else; refuse rather than merge the flop with itself.
	if (drv == named) {
		if (error)
			refuse("Input %s of cell %s is only partly driven by flop %s.\n",
					log_id(port), log_id(cell), log_id(named));
		return false;
	}

	FfData ff(&initvals, drv);
	if (const char *why = mismatch_reason(sigmap, ref, ff)) {
		if (error)
			refuse("Flop %s on input %s of cell %s has %s flop %s.\n",
					log_id(drv), log_id(port), log_id(cell), why, log_id(named));
		return false;
	}
	if (const char *why = unmovable_reason(ff)) {
		if (error)
			refuse("Flop %s on input %s of cell %s cannot be merged because %s.\n",
					log_id(drv), log_id(port), log_id(cell), why);
		return false;
	}
	desc.push_back({PortBit::Flop, 0, drv, it->second.offset, State::S0});
	return true;
}

// Classify every bit of cell.port relative to the after-path signal path_sig.
// The whole path has to enter this port. Bits of the port that are not on the
// path must be sibling flops matching ref, or constants. That is what makes
// f(reg(x), reg(y)) a legal forward move when x and y were bit-blasted into
// separate WIDTH=1 registers instead of one wide flop.
bool describe_port(SigMap &sigmap, const dict<SigBit, BitSrc> &drivers,
		FfInitVals &initvals, FfData &ref, Cell *named,
		Cell *cell, IdString port, const SigSpec &path_sig,
		std::vector<PortBit> &desc, bool error)
{
	desc.clear();
	if (!is_data_input(cell, port))
		return false;

	SigSpec mapped = sigmap(cell->getPort(port));
	dict<SigBit, int> path_index;
	for (int i = 0; i < GetSize(path_sig); i++) {
		if (!path_sig[i].is_wire())
			return false;
		path_index[path_sig[i]] = i;
	}

	int overlap = 0;
	for (int i = 0; i < GetSize(mapped); i++)
		if (mapped[i].is_wire() && path_index.count(mapped[i]))
			overlap++;
	if (overlap == 0 || overlap != GetSize(path_sig))
		return false;

	int seen_path = 0;
	for (auto bit : mapped) {
		if (bit.is_wire() && path_index.count(bit)) {
			desc.push_back({PortBit::Path, path_index[bit], nullptr, 0, State::S0});
			seen_path++;
			continue;
		}
		if (!classify_off_path_bit(sigmap, drivers, initvals, ref, named, cell,
				port, bit, desc, error))
			return false;
	}

	return seen_path == GetSize(path_sig) && seen_path > 0;
}

// A data input that is not the after-path: every bit is a sibling flop or a
// constant. Used for the other operand of $add/$mul/$mux once the path port
// has been identified.
bool describe_operand(SigMap &sigmap, const dict<SigBit, BitSrc> &drivers,
		FfInitVals &initvals, FfData &ref, Cell *named,
		Cell *cell, IdString port, std::vector<PortBit> &desc, bool error)
{
	desc.clear();
	for (auto bit : sigmap(cell->getPort(port)))
		if (!classify_off_path_bit(sigmap, drivers, initvals, ref, named, cell,
				port, bit, desc, error))
			return false;
	return true;
}

Cell *next_on_path(Module *module, SigMap &sigmap, const dict<SigBit, BitSrc> &drivers,
		FfInitVals &initvals, FfData &ref, Cell *named, const SigSpec &cur,
		IdString &port)
{
	Cell *found = nullptr;
	port = IdString();
	int hits = 0;
	for (auto cell : module->cells()) {
		for (auto cand : data_inputs(cell)) {
			std::vector<PortBit> desc;
			if (!describe_port(sigmap, drivers, initvals, ref, named, cell, cand,
					cur, desc, false))
				continue;
			hits++;
			found = cell;
			port = cand;
		}
	}
	if (hits != 1)
		return nullptr;
	return found;
}

Const stored_bit(FfInitVals &initvals, Cell *flop, int offset, FoldKind kind)
{
	FfData ff(&initvals, flop);
	Const val;
	switch (kind) {
	case FoldKind::Srst:
		val = ff.val_srst;
		break;
	case FoldKind::Arst:
		val = ff.val_arst;
		break;
	case FoldKind::Aload:
		log_assert(ff.has_aload);
		log_assert(ff.sig_ad.is_fully_const());
		val = ff.sig_ad.as_const();
		break;
	default:
		val = ff.val_init;
		break;
	}
	log_assert(offset >= 0 && offset < GetSize(val));
	return Const(val[offset]);
}

Const assemble_const(const std::vector<PortBit> &desc, const Const &cur,
		FfInitVals &initvals, FoldKind kind)
{
	std::vector<State> bits;
	bits.reserve(GetSize(desc));
	for (auto &bit : desc) {
		if (bit.kind == PortBit::Path)
			bits.push_back(cur[bit.path_offset]);
		else if (bit.kind == PortBit::Const)
			bits.push_back(bit.st);
		else
			bits.push_back(stored_bit(initvals, bit.flop, bit.q_offset, kind)[0]);
	}
	return Const(bits);
}

std::vector<ChainStep> collect_chain(Module *module, SigMap &sigmap,
		const dict<SigBit, BitSrc> &drivers, FfInitVals &initvals, FfData &ref,
		Cell *flop, Cell *cut)
{
	std::vector<ChainStep> chain;
	pool<Cell *> seen;
	SigSpec q = sigmap(flop->getPort(ID::Q));

	// First hop: any data-input port that consumes all of Q, including a
	// wide port that only slices Q as one bit among sibling flop Qs. Extra
	// readers of Q (full or partial) do not disqualify the hop; they only
	// mean a copy is left behind, which is apply_move's decision.
	ChainStep first = {};
	int paths = 0;
	for (auto cell : module->cells()) {
		for (auto port : data_inputs(cell)) {
			std::vector<PortBit> desc;
			bool error = cell == cut;
			if (!describe_port(sigmap, drivers, initvals, ref, flop, cell, port,
					q, desc, error))
				continue;
			if (!reaches_cut(module, sigmap, drivers, initvals, ref, flop, cell, cut))
				continue;
			paths++;
			first = {cell, port};
		}
	}
	if (paths == 0)
		refuse("Cut %s is not on the after-path of flop %s.\n", log_id(cut), log_id(flop));
	if (paths > 1)
		refuse("Cut %s is reachable from flop %s on more than one path.\n",
				log_id(cut), log_id(flop));

	seen.insert(first.cell);
	chain.push_back(first);
	if (first.cell == cut)
		return chain;

	SigSpec cur = sigmap(first.cell->getPort(ID::Y));
	while (true) {
		IdString port;
		Cell *next = next_on_path(module, sigmap, drivers, initvals, ref, flop, cur, port);
		if (!next)
			break;

		if (seen.count(next))
			refuse("Cycle on the after-path of flop %s.\n", log_id(flop));
		seen.insert(next);
		chain.push_back({next, port});
		if (next == cut)
			break;
		if (!next->hasPort(ID::Y))
			break;
		cur = sigmap(next->getPort(ID::Y));
	}

	if (chain.back().cell != cut)
		refuse("Cut %s is not on the after-path of flop %s.\n", log_id(cut), log_id(flop));
	return chain;
}

// Controls a move cannot relocate. Both of these load a value into the register
// from a net rather than from a parameter, so carrying them across a cut would
// mean building logic to transform that net rather than folding a constant.
//
// An async load with a constant AD is the same as an async reset value: the
// enable is a net that travels with the register, and the value folds. Ibex
// encodes async reset that way ($aldff + AD=0).
//
// A clock enable is deliberately absent: it stores no value of its own, it only
// decides whether the register updates. Holding commutes with a pure function,
// since f of an unchanged input is an unchanged f, so the enable travels with
// the register untouched.
const char *unmovable_reason(FfData &ff)
{
	if (ff.has_aload && !ff.sig_ad.is_fully_const())
		return "it has an async load from a net";
	if (ff.has_sr)
		return "it has a set/reset";
	return nullptr;
}

const char *fold_kind_name(FoldKind kind)
{
	switch (kind) {
	case FoldKind::Srst:
		return "sync reset";
	case FoldKind::Arst:
		return "async reset";
	case FoldKind::Aload:
		return "async load";
	default:
		return "init";
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
// is not a special case here. A bit-sliced operand is assembled bit by bit:
// path bits from cur, sibling bits from those flops' stored values, constants
// as themselves.
Const fold_value(Module *, SigMap &sigmap, const dict<SigBit, BitSrc> &drivers,
		FfInitVals &initvals, FfData &ref, Cell *flop,
		const std::vector<ChainStep> &chain, FoldKind kind, Const cur)
{
	SigSpec path = sigmap(flop->getPort(ID::Q));
	for (auto &step : chain) {
		if (is_buf(step.cell)) {
			path = sigmap(step.cell->getPort(ID::Y));
			continue;
		}

		std::vector<Const> args;
		for (auto port : data_inputs(step.cell)) {
			std::vector<PortBit> desc;
			bool ok;
			if (port == step.port)
				ok = describe_port(sigmap, drivers, initvals, ref, flop, step.cell, port,
						path, desc, true);
			else
				ok = describe_operand(sigmap, drivers, initvals, ref, flop, step.cell, port,
						desc, true);
			if (!ok)
				refuse("Input %s of cell %s is not on the after-path of flop %s.\n",
						log_id(port), log_id(step.cell), log_id(flop));
			args.push_back(assemble_const(desc, cur, initvals, kind));
		}

		bool err = false;
		Const out;
		if (GetSize(args) == 3)
			out = CellTypes::eval(step.cell, args[0], args[1], args[2], &err);
		else if (GetSize(args) == 2)
			out = CellTypes::eval(step.cell, args[0], args[1], &err);
		else
			out = CellTypes::eval(step.cell, args[0], Const(), &err);
		if (err)
			refuse("Flop %s has a %s value that opt_retime cannot fold through "
					"cell %s, because it cannot evaluate %s on constants.\n",
					log_id(flop), fold_kind_name(kind), log_id(step.cell),
					log_id(step.cell->type));
		cur = out;
		path = sigmap(step.cell->getPort(ID::Y));
	}
	return cur;
}

// Fold one kind of stored value through the chain, if there is one to fold.
// Returns false when every copy of it is undefined, meaning there is nothing to
// carry. A mix of defined and undefined copies is refused rather than folded:
// evaluating one against the other gives undefined bits back, which would
// quietly discard what the defined side said.
bool fold_through(Module *module, SigMap &sigmap, const dict<SigBit, BitSrc> &drivers,
		FfInitVals &initvals, FfData &ref, Cell *flop,
		const std::vector<ChainStep> &chain, FoldKind kind, Const start, Const &result)
{
	bool any = !start.is_fully_undef();
	bool all = start.is_fully_def();
	SigSpec path = sigmap(flop->getPort(ID::Q));
	for (auto &step : chain) {
		if (is_buf(step.cell)) {
			path = sigmap(step.cell->getPort(ID::Y));
			continue;
		}
		for (auto port : data_inputs(step.cell)) {
			std::vector<PortBit> desc;
			if (port == step.port)
				describe_port(sigmap, drivers, initvals, ref, flop, step.cell, port,
						path, desc, true);
			else
				describe_operand(sigmap, drivers, initvals, ref, flop, step.cell, port,
						desc, true);
			for (auto &bit : desc) {
				if (bit.kind != PortBit::Flop)
					continue;
				Const val = stored_bit(initvals, bit.flop, bit.q_offset, kind);
				any = any || !val.is_fully_undef();
				all = all && val.is_fully_def();
			}
		}
		path = sigmap(step.cell->getPort(ID::Y));
	}
	if (!any)
		return false;
	if (!all)
		refuse("Flop %s cannot move because the move would fold %s values together "
				"and only some of them are defined.\n", log_id(flop), fold_kind_name(kind));
	result = fold_value(module, sigmap, drivers, initvals, ref, flop, chain, kind, start);
	return true;
}

// The stored values a register carries through a move. All four travel the
// same way and are written back onto the flop the same way, so a direction
// only has to say how one constant makes the trip.
struct StoredValues {
	Const init, srst, arst, aload;
	bool got_init = false, got_srst = false, got_arst = false, got_aload = false;

	// fold is handed one kind and its starting value, and either fills in the
	// result or reports that there was nothing to carry.
	template <typename Fold> void collect(FfData &ff, Fold fold)
	{
		got_init = fold(FoldKind::Init, ff.val_init, init);
		got_srst = ff.has_srst && fold(FoldKind::Srst, ff.val_srst, srst);
		got_arst = ff.has_arst && fold(FoldKind::Arst, ff.val_arst, arst);
		got_aload = ff.has_aload && ff.sig_ad.is_fully_const() &&
				fold(FoldKind::Aload, ff.sig_ad.as_const(), aload);
	}

	// Write the results back at the register's new width. Undefined values
	// still have to be resized, or emitting a widened register would assert
	// on their width.
	void apply(FfData &ff, int width) const
	{
		ff.val_init = got_init ? init : Const(State::Sx, width);
		if (ff.has_srst)
			ff.val_srst = got_srst ? srst : Const(State::Sx, width);
		if (ff.has_arst)
			ff.val_arst = got_arst ? arst : Const(State::Sx, width);
		if (ff.has_aload) {
			if (got_aload)
				ff.sig_ad = SigSpec(aload);
			else if (ff.sig_ad.is_fully_const())
				ff.sig_ad = Const(State::Sx, width);
		}
	}

	void log_folds(IdString flop_name) const
	{
		if (got_init)
			log("Folded init value of flop %s to %s.\n",
					log_id(flop_name), log_signal(init));
		if (got_srst)
			log("Folded sync reset value of flop %s to %s.\n",
					log_id(flop_name), log_signal(srst));
		if (got_arst)
			log("Folded async reset value of flop %s to %s.\n",
					log_id(flop_name), log_signal(arst));
		if (got_aload)
			log("Folded async load value of flop %s to %s.\n",
					log_id(flop_name), log_signal(aload));
	}
};

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
	if (ff.has_aload) {
		if (sigmap(ff.sig_aload) != sigmap(ref.sig_aload))
			return "a different async load net than";
		if (ff.pol_aload != ref.pol_aload)
			return "an async load of the opposite polarity to";
	}
	// Widths are deliberately not compared: a $mux merges a 1-bit select
	// register with its wide data registers.
	return nullptr;
}

// A forward move across a multi-input cell folds every other data input into
// the register it leaves behind. Bit-sliced operands contribute one merge per
// sibling flop. The flop is deleted only when nothing else reads it; extra
// readers keep the flop and only the cut is rewired to D, which is the same
// netlist as cloning a fanout-1 copy and merging that copy away.
std::vector<Merge> collect_merges(Module *module, SigMap &sigmap,
		const dict<SigBit, BitSrc> &drivers, FfInitVals &initvals, Cell *flop,
		FfData &ref, const std::vector<ChainStep> &chain)
{
	std::vector<Merge> merges;
	pool<Cell *> seen;
	SigSpec path = sigmap(flop->getPort(ID::Q));
	for (auto &step : chain) {
		for (auto port : data_inputs(step.cell)) {
			std::vector<PortBit> desc;
			if (port == step.port)
				describe_port(sigmap, drivers, initvals, ref, flop, step.cell, port,
						path, desc, true);
			else
				describe_operand(sigmap, drivers, initvals, ref, flop, step.cell, port,
						desc, true);
			for (auto &bit : desc) {
				if (bit.kind != PortBit::Flop || seen.count(bit.flop))
					continue;
				seen.insert(bit.flop);
				bool keep = has_other_readers(module, sigmap,
						sigmap(bit.flop->getPort(ID::Q)), step.cell, port);
				merges.push_back({bit.flop, step.cell, port, bit.flop->getPort(ID::D), keep});
			}
		}
		if (step.cell->hasPort(ID::Y))
			path = sigmap(step.cell->getPort(ID::Y));
	}
	return merges;
}

void check_controls(FfData &ff, SigMap &sigmap, const pool<SigBit> &forbidden)
{
	auto check = [&](const SigSpec &sig, const char *what) {
		if (touches(sigmap, forbidden, sig))
			refuse("Flop %s control %s uses a data wire being retimed.\n", log_id(ff.cell), what);
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

// Types a backward move can invert: some x with f(x, others) equal to the value
// the flop stores. The preimage need not be unique, only exist, since the move
// only has to reproduce that value on the first cycle, so $and and $or count
// even though they lose information, and $mul counts even though an even
// constant has no inverse. $eq and $reduce_* stay out because they also
// resize the flop.
//
// $mux is here because nothing about the identity reg(f(x)) = f(reg(x)) cares
// how many operands f has: reg(S ? B : A) is (reg S) ? (reg B) : (reg A), with
// a clone on each of the two operands the path does not enter on. What the
// extra operand does cost is cycle 0, and the select is what pays for it: a
// clone of the select that starts at the constant picking the path port makes
// the mux reproduce the stored value whatever the other data clone holds.
//
// A constant other operand is a meet: f(reg(x), c) equals reg(f(x, c)) and
// nothing is cloned. A live other operand is the same transform with a clone of
// the flop on that input.
bool is_invertible_backward(Cell *cell)
{
	return cell->type.in(ID($buf), ID($_BUF_), ID($not), ID($add), ID($sub),
			ID($mul), ID($xor), ID($xnor), ID($and), ID($or), ID($mux));
}

bool sig_all_wires(const SigSpec &sig)
{
	if (GetSize(sig) == 0)
		return false;
	for (auto bit : sig)
		if (!bit.is_wire())
			return false;
	return true;
}

bool driven_by_ff(const dict<SigBit, BitSrc> &drivers, const SigSpec &sig)
{
	if (!sig_all_wires(sig))
		return false;
	for (auto bit : sig) {
		auto it = drivers.find(bit);
		if (it == drivers.end() || it->second.port != ID::Q ||
				!it->second.cell->is_builtin_ff())
			return false;
	}
	return true;
}

// Driver of every bit of sig, requiring sig to be that port in full. A slice
// of a wide Y into a narrower D is a different transform.
Cell *unique_full_driver(const dict<SigBit, BitSrc> &drivers, SigMap &sigmap,
		const SigSpec &sig, IdString &port)
{
	port = IdString();
	if (GetSize(sig) == 0)
		return nullptr;
	Cell *cell = nullptr;
	for (int i = 0; i < GetSize(sig); i++) {
		if (!sig[i].is_wire())
			return nullptr;
		auto it = drivers.find(sig[i]);
		if (it == drivers.end())
			return nullptr;
		if (i == 0) {
			cell = it->second.cell;
			port = it->second.port;
		} else if (it->second.cell != cell || it->second.port != port)
			return nullptr;
	}
	if (sigmap(cell->getPort(port)) != sig)
		return nullptr;
	return cell;
}

bool cell_signed(Cell *cell, IdString param)
{
	return cell->hasParam(param) && cell->getParam(param).as_bool();
}

// The live data input a backward move slides the named flop onto. Constants
// stay: f(reg(x), c) is reg(f(x, c)) and nothing is cloned. Every other live
// input gets a clone of the flop, at any hop of the chain and not just at the
// cut, which is what lets the move walk back through a whole mux tree instead
// of stopping at the first level with a live select. A unique live input that
// is already a flop is stacking, not cloning, and is refused.
//
// Only the port the flop slides onto has to be a net the flop can take over in
// full, so being partly constant rules a port out of being the path but not out
// of being cloned: a clone's D carries the constant bits along with the wires,
// the same way a forward move classifies a mixed operand bit by bit.
IdString backward_path_port(SigMap &sigmap, const dict<SigBit, BitSrc> &drivers,
		Cell *cell, Cell *flop)
{
	IdString path, first_ff, first_mixed;
	int live = 0;
	for (auto port : data_inputs(cell)) {
		SigSpec sig = sigmap(cell->getPort(port));
		if (sig.is_fully_const())
			continue;
		live++;
		if (!sig_all_wires(sig)) {
			if (first_mixed == IdString())
				first_mixed = port;
			continue;
		}
		if (driven_by_ff(drivers, sig)) {
			if (first_ff == IdString())
				first_ff = port;
			continue;
		}
		if (path == IdString())
			path = port;
	}
	if (live == 0)
		refuse("Every data input of cell %s is constant, so flop %s has "
				"nothing to slide onto.\n", log_id(cell), log_id(flop));
	// An input that is already registered is not stacking, because the move
	// does not leave a register behind on it: the flop slides off the net it
	// was on, and whatever registered the input is then the only register on
	// that path. The plain-wire preference above still wins, so this only
	// decides where to land when every live input is registered -- an
	// accumulator entered on its own feedback operand, or a $buf chain whose
	// far end is another flop's Q.
	if (path == IdString())
		path = first_ff;
	if (path == IdString())
		refuse("Input %s of cell %s is only partly a wire, so flop %s "
				"cannot move backward onto it.\n",
				log_id(first_mixed), log_id(cell), log_id(flop));
	// Sliding onto a select is a different problem from sliding onto a data
	// port. The clone that makes cycle 0 work is the select's, and there is no
	// select clone left to place: the two data clones would both have to start
	// at the stored value rather than at a fixed identity, which is a per-fold
	// starting value and not what clone_start hands out.
	if (cell->type == ID($mux) && path == ID::S)
		refuse("Both data inputs of %s are constant, already registered, or "
				"only partly a wire, so flop %s would have to slide onto the "
				"select, which opt_retime does not do yet.\n",
				log_id(cell), log_id(flop));
	return path;
}

// What a cloned flop starts at: a value that makes the cell an identity on the
// path port, so the path flop can hold the old stored value itself and f still
// reproduces it. This is per port and not just per cell type, because a $mux
// reaches identity on two ports at once and asks something different of each.
Const clone_start(Cell *cell, IdString path_port, IdString clone_port, int width)
{
	if (cell->type == ID($mux)) {
		// The select is the whole cycle-0 argument: pin it at the constant
		// that picks the path port and the mux is that port, whatever the
		// other data clone came up holding. So that one is a don't-care.
		if (clone_port == ID::S)
			return Const(path_port == ID::A ? State::S0 : State::S1, width);
		return Const(State::Sx, width);
	}
	// x & 1s and ~(x ^ 1s) are both x; $mul is identity at 1; the rest are
	// identity at 0.
	if (cell->type == ID($mul))
		return Const(1, width);
	bool ones = cell->type.in(ID($and), ID($xnor));
	return Const(ones ? State::S1 : State::S0, width);
}

// x * other = y in the low `len` bits. other is extended the way $mul would,
// then inverted in Z/2^len Z. An odd other has one preimage; an even one has
// several, or none. Any preimage will do, and a y that is out of reach is
// left for invert_step's forward check to refuse.
Const mul_preimage(const Const &y, const Const &other, bool other_signed, int len)
{
	Const c = const_pos(other, Const(), other_signed, false, len);
	int tz = 0;
	while (tz < len && c[tz] == State::S0)
		tz++;
	if (tz == len)
		return Const(State::S0, len);
	for (int i = 0; i < tz; i++)
		if (y[i] != State::S0)
			return y;

	int n = len - tz;
	Const amt(tz, 32);
	Const c_odd = const_shr(c, amt, false, false, n);
	Const y_shr = const_shr(y, amt, false, false, n);
	// Hensel: start at 1 and double the number of correct bits each step.
	Const inv(1, n);
	Const two(2, n);
	for (int ok = 1; ok < n; ok *= 2)
		inv = const_mul(inv, const_sub(two, const_mul(c_odd, inv, false, false, n),
				false, false, n), false, false, n);
	return const_pos(const_mul(y_shr, inv, false, false, n), Const(), false, false, len);
}

// Solve f(..., x, ...) = y for the path operand x. y is the stored value on the
// output side of this cell; others holds, per port, the constant still wired to
// that operand or the clone_start of the flop being cloned onto it. It is keyed
// by port rather than being the one other operand because a $mux has two.
// Any preimage will do, since the move only has to reproduce y on the first
// cycle, so $and and $or answer with y itself: the bits their other operand
// pins are already y's own, and the rest pass straight through. $mux answers
// the same way, for the same reason turned inside out: its select is pinned to
// pick the path port, so the path port is the output and y is its own preimage.
// $mul answers with y times the modular inverse of the other operand; an even
// other has several preimages or none, and the forward check refuses a y that
// is out of reach.
Const invert_step(Cell *cell, IdString path_port, Const y,
		const dict<IdString, Const> &others)
{
	auto operand = [&](IdString port) {
		auto it = others.find(port);
		return it == others.end() ? Const() : it->second;
	};

	int len = GetSize(cell->getPort(path_port));
	if (GetSize(cell->getPort(ID::Y)) != len)
		refuse("Cell %s has Y width %d and path port %s width %d; a "
				"backward move cannot invert a width change yet.\n",
				log_id(cell), GetSize(cell->getPort(ID::Y)),
				log_id(path_port), len);
	if (is_buf(cell))
		return y;

	Const other = operand(path_port == ID::A ? ID::B : ID::A);
	bool sa = cell_signed(cell, ID::A_SIGNED);
	bool sb = cell_signed(cell, ID::B_SIGNED);
	Const x;
	if (cell->type == ID($not))
		x = const_not(y, Const(), false, false, len);
	else if (cell->type == ID($xor))
		x = const_xor(y, other, false, false, len);
	else if (cell->type == ID($xnor))
		x = const_xnor(y, other, false, false, len);
	else if (cell->type == ID($add))
		x = const_sub(y, other, sa, sb, len);
	else if (cell->type == ID($sub) && path_port == ID::A)
		x = const_add(y, other, sa, sb, len);
	else if (cell->type == ID($sub) && path_port == ID::B)
		x = const_sub(other, y, sa, sb, len);
	else if (cell->type == ID($mul))
		x = mul_preimage(y, other, path_port == ID::A ? sb : sa, len);
	else if (cell->type.in(ID($and), ID($or), ID($mux)))
		x = y;
	else
		refuse("Cell %s has type %s, which opt_retime cannot invert yet.\n",
				log_id(cell), log_id(cell->type));

	// Running the cell forward on the candidate is the whole argument that a
	// lossy type is safe here, and it catches a mask or an x bit that leaves y
	// out of reach entirely. For $mux it also catches a select wired to a
	// constant that picks the port the path did not come in on.
	bool err = false;
	Const back;
	if (cell->type == ID($mux))
		back = CellTypes::eval(cell, path_port == ID::A ? x : operand(ID::A),
				path_port == ID::B ? x : operand(ID::B),
				operand(ID::S), &err);
	else
		back = path_port == ID::A ? CellTypes::eval(cell, x, other, &err)
				: CellTypes::eval(cell, other, x, &err);
	if (err || back != y)
		refuse("Cell %s has no input on %s that produces %s, so a "
				"backward move has no stored value to leave behind.\n",
				log_id(cell), log_id(path_port), log_signal(y));
	return x;
}

// What reads a hop's Y besides the path, and so has to be served the undelayed
// value from a duplicate. A cell port is served by pointing it at the duplicate;
// a module output has no port to point, so that hop hands the duplicate the
// original net instead and takes a fresh one for the delayed value.
struct OffPath {
	std::vector<CellPort> readers;
	bool output = false;

	bool empty() const { return readers.empty() && !output; }
};

// From start back to cut: each hop's Y drives the next hop's path port (or
// start, for the first). chain.front() is the cell driving start, chain.back()
// is the cut. extra comes back parallel to the chain, holding what reads each
// hop's Y off the path.
//
// start is flop's D, or the bits of it being moved when the flop is several
// registers sharing a cell. It is passed rather than read off the flop so that
// slice_for_cut can ask where each run of D leads without moving anything.
std::vector<ChainStep> collect_backward_chain(Module *module, SigMap &sigmap,
		const dict<SigBit, BitSrc> &drivers, Cell *flop, const SigSpec &start,
		Cell *cut, std::vector<OffPath> &extra)
{
	extra.clear();
	std::vector<ChainStep> chain;
	pool<Cell *> seen;
	Cell *reader = flop;
	IdString reader_port = ID::D;
	SigSpec cur = sigmap(start);

	while (true) {
		IdString y_port;
		Cell *cell = unique_full_driver(drivers, sigmap, cur, y_port);
		if (cell == nullptr || y_port != ID::Y)
			refuse("The before-path of flop %s is not a unique cell Y at %s.\n",
					log_id(flop), log_signal(cur));
		if (!is_invertible_backward(cell))
			refuse("Cut cell %s has type %s, which opt_retime cannot move "
					"backward across yet.\n",
					log_id(cell), log_id(cell->type));

		// Readers of Y that are not the path do not stop the move; the cell is
		// duplicated for them. The flop is the one reader that cannot be served
		// that way: it is rebuilt at the end from the FfData snapshot taken
		// before any rewiring, which would bring its original control nets back
		// with it and undo the substitution.
		std::vector<CellPort> others;
		bool drives_output = false;
		scan_extra_readers(module, sigmap, sigmap(cell->getPort(ID::Y)),
				reader, reader_port, others, drives_output);
		for (auto &rd : others)
			if (rd.cell == flop)
				refuse("Flop %s reads Y of cell %s on port %s as well as on its "
						"before-path, so it cannot move backward across it.\n",
						log_id(flop), log_id(cell), log_id(rd.port));

		if (seen.count(cell))
			refuse("Cycle on the before-path of flop %s.\n", log_id(flop));
		seen.insert(cell);

		IdString path_port = backward_path_port(sigmap, drivers, cell, flop);
		chain.push_back({cell, path_port});
		extra.push_back({others, drives_output});
		if (cell == cut)
			return chain;
		reader = cell;
		reader_port = path_port;
		cur = sigmap(cell->getPort(path_port));
	}
}

// The checks both directions make on the chain once it is known. Every hop
// needs a Y to rewire; the chain walk follows a port that consumes the whole
// path, so a 1-bit Q may enter a wide $mul.A as one slice among sibling flops,
// and the register still takes the width of the cut output.
//
// Every cell on the chain except a $buf transforms the values the register
// loads, and the ones unmovable_reason names arrive on a net rather than as a
// constant, so there is nothing to fold and the move is refused. A $buf passes
// them through untouched and needs no such check.
void check_chain(FfData &ff, Cell *flop, const std::vector<ChainStep> &chain)
{
	for (auto &step : chain)
		if (!step.cell->hasPort(ID::Y))
			refuse("Cell %s is missing port Y.\n", log_id(step.cell));

	for (auto &step : chain)
		if (!is_buf(step.cell))
			if (const char *why = unmovable_reason(ff))
				refuse("Flop %s cannot move across cell %s because %s, which the "
						"move would have to push through the cell.\n",
						log_id(flop), log_id(step.cell), why);
}

// Which bits of flop are the register the caller meant. A wide cell can be
// several independent registers, which is what an RTL array declaration leaves
// behind: one $aldff of width 320 whose D is a concat of ten drivers and whose Q
// is a concat of ten wires, holding ten 32-bit words that share nothing but a
// clock. opt_retime moves whole cells, and a D with ten drivers has no unique
// cell behind it, so every word of such a register is refused before the move
// starts.
//
// D is cut at the bits where its driver changes, which is the rule splitcells
// uses and which lands on the word boundaries by itself. The -cut names which
// run to take: the caller gave both ends of the move, so the run whose
// before-path reaches the cut is the register that was meant, and nothing has to
// read the flop's name to work out which word it is.
//
// A register that is a single run comes back whole, which is the ordinary case
// and leaves the move exactly as it was.
std::vector<int> slice_for_cut(Module *module, SigMap &sigmap,
		const dict<SigBit, BitSrc> &drivers, Cell *flop, Cell *cut)
{
	SigSpec d = sigmap(flop->getPort(ID::D));
	std::vector<std::vector<int>> runs;
	Cell *prev = nullptr;
	for (int i = 0; i < GetSize(d); i++) {
		auto it = drivers.find(d[i]);
		Cell *driver = it == drivers.end() ? nullptr : it->second.cell;
		// An undriven bit joins nothing: it cannot be part of a run that has a
		// unique cell behind it, and starting a fresh run keeps it from
		// swallowing the next one.
		if (runs.empty() || driver == nullptr || driver != prev)
			runs.push_back({});
		runs.back().push_back(i);
		prev = driver;
	}

	std::vector<int> all;
	for (int i = 0; i < GetSize(d); i++)
		all.push_back(i);
	if (GetSize(runs) < 2)
		return all;

	// The chain walk is the authority on whether a run reaches the cut, so it is
	// what gets asked, rather than a second walk that could disagree with it.
	// It refuses by throwing, and a run that refuses is simply not this move.
	std::vector<int> found;
	int reaching = 0;
	for (auto &run : runs) {
		SigSpec start;
		for (int i : run)
			start.append(d[i]);
		std::vector<OffPath> extra;
		try {
			collect_backward_chain(module, sigmap, drivers, flop, start, cut, extra);
		} catch (const MoveRefused &) {
			continue;
		}
		if (reaching++ == 0)
			found = run;
	}

	if (reaching == 1)
		return found;
	if (reaching == 0)
		refuse("Flop %s is %d registers sharing one cell, and the before-path of "
				"none of them reaches cut %s.\n",
				log_id(flop), GetSize(runs), log_id(cut));
	refuse("Flop %s is %d registers sharing one cell and %d of them reach cut %s, "
			"so opt_retime cannot tell which one to move.\n",
			log_id(flop), GetSize(runs), reaching, log_id(cut));
}

// The bits of a width-wide register that keep is not taking.
std::vector<int> other_bits(const std::vector<int> &keep, int width)
{
	pool<int> taken(keep.begin(), keep.end());
	std::vector<int> rest;
	for (int i = 0; i < width; i++)
		if (!taken.count(i))
			rest.push_back(i);
	return rest;
}

// A cell holds more than one register when its D arrives in several pieces:
// each piece is driven on its own and nothing ties them together but the clock.
// This is a look at the port rather than a walk of the module, so it is cheap
// enough to ask anywhere, and it errs the safe way -- a D that arrives whole is
// one register for every purpose here, whatever its width.
void refuse_if_shared(Cell *flop, const char *what)
{
	if (!flop->hasPort(ID::D))
		return;
	int pieces = GetSize(flop->getPort(ID::D).chunks());
	if (pieces > 1)
		refuse("Flop %s is %d registers sharing one cell, which opt_retime can "
				"take apart for a plain -backward move but not for %s yet.\n",
				log_id(flop), pieces, what);
}

// dry_run asks the question and skips the answer: every refusal this move can
// make has been made by the time the first cell is touched, so returning there
// leaves a legality check with no side effects. -all-fanouts is what wants it,
// having several moves to make and no way to take the earlier ones back.
void apply_backward_move(Module *module, Cell *flop, Cell *cut, bool dry_run = false)
{
	if (!flop->is_builtin_ff())
		refuse("Cell %s is not a built-in flip-flop.\n", log_id(flop));
	if (data_inputs(cut).empty())
		refuse("Cut cell %s has type %s, which opt_retime cannot move across yet.\n",
				log_id(cut), log_id(cut->type));
	if (flop == cut)
		refuse("Flop and cut must be different cells.\n");

	SigMap sigmap(module);
	FfInitVals initvals(&sigmap, module);

	FfData whole(&initvals, flop);
	if (!whole.has_clk || !flop->hasPort(ID::D) || !flop->hasPort(ID::Q))
		refuse("Cell %s is not a clocked flop with D and Q.\n", log_id(flop));

	dict<SigBit, BitSrc> drivers = index_output_bits(module, sigmap);

	// Everything below works on one register. When the cell holds several, that
	// is the run the cut picked; the rest of the cell is put back beside the
	// move at the end. The slice is a value and builds nothing, so a refusal
	// between here and the commit still leaves the design untouched.
	std::vector<int> bits = slice_for_cut(module, sigmap, drivers, flop, cut);
	bool sliced = GetSize(bits) != whole.width;
	FfData ff = sliced ? whole.slice(bits) : whole;
	// The register the caller named is the one that moves, so it keeps the name
	// and the remainder takes a new one. FfData::slice hands out a fresh id.
	if (sliced)
		ff.name = whole.name;

	std::vector<OffPath> extra;
	std::vector<ChainStep> chain = collect_backward_chain(module, sigmap, drivers,
			flop, ff.sig_d, cut, extra);

	check_chain(ff, flop, chain);

	if (chain.back().cell != cut)
		refuse("Cut %s is not on the before-path of flop %s.\n",
				log_id(cut), log_id(flop));

	// A duplicate reads the duplicate of the hop below it, and nothing else on
	// the chain, so a chain cell reading another hop off the path would need
	// the same substitution made on the duplicate's own operands. That is not
	// done, so reconvergence inside the chain is refused rather than wired up
	// to the delayed copy by mistake.
	pool<Cell *> chain_cells;
	for (auto &step : chain)
		chain_cells.insert(step.cell);
	int dup_from = GetSize(chain);
	for (int i = 0; i < GetSize(chain); i++) {
		for (auto &rd : extra[i].readers)
			if (chain_cells.count(rd.cell))
				refuse("Cell %s is on the before-path of flop %s and also reads "
						"Y of %s off it, which opt_retime cannot duplicate "
						"yet.\n", log_id(rd.cell), log_id(flop),
						log_id(chain[i].cell));
		if (!extra[i].empty() && i < dup_from)
			dup_from = i;
	}

	// Which ports of which hop get a clone, one set per chain step. A clone at
	// an intermediate hop is what makes a mux tree worth walking: the whole
	// chain slides back one cycle in a single rewiring, and each clone delays
	// its own operand by that same cycle, so every level is a level of depth
	// removed rather than only the one at the cut.
	std::vector<pool<IdString>> clone_ports(GetSize(chain));
	for (int i = 0; i < GetSize(chain); i++) {
		for (auto port : data_inputs(chain[i].cell)) {
			if (port == chain[i].port)
				continue;
			SigSpec sig = sigmap(chain[i].cell->getPort(port));
			if (sig.is_fully_const())
				continue;
			clone_ports[i].insert(port);
		}
	}

	IdString path_port = chain.back().port;
	Cell *front = chain.front().cell;
	SigSpec path_in = cut->getPort(path_port);
	SigSpec d = ff.sig_d;
	SigSpec q = ff.sig_q;

	if (GetSize(path_in) != GetSize(q))
		refuse("Backward move across %s would resize flop %s from %d to %d "
				"bits, which is not supported yet.\n",
				log_id(cut), log_id(flop), GetSize(q), GetSize(path_in));

	// A $mux select is one bit while the flop is WIDTH, so that one clone is
	// allowed to come out narrower than the flop. FfData carries the width per
	// clone, and the per-bit control signals that would not survive being
	// resized - set/reset, and an async load arriving on a net - are refused
	// upstream by unmovable_reason, so there is nothing left for a narrow clone
	// to get wrong. Every other port is still held to the flop's width, as is
	// the path input above, so a wide mux cannot slide onto its select.
	for (int i = 0; i < GetSize(chain); i++)
		for (auto port : clone_ports[i]) {
			Cell *cell = chain[i].cell;
			int n = GetSize(cell->getPort(port));
			if (n == GetSize(q))
				continue;
			if (cell->type == ID($mux) && port == ID::S && n == 1)
				continue;
			refuse("Backward move across %s would clone flop %s onto "
					"input %s of %s of width %d, from %d bits, which is "
					"not supported yet.\n",
					log_id(cut), log_id(flop), log_id(port),
					log_id(cell), n, GetSize(q));
		}

	// A path input or a clone that reads the flop's own Q used to be refused as
	// a second register in the flop's own loop. It is not one. The commit below
	// points the first hop's Y at the old Q net, and that hop computes at t what
	// it used to compute at t-1, which is exactly what the register held at t.
	// So Q keeps its value on every cycle while ceasing to be a register, the
	// clone reading it becomes the one register on the feedback arm, and each
	// loop comes out with the register count it went in with. opt_retime_holdloop
	// proves both shapes: a clone on the hold arm of an enable mux, and a path
	// input that is the flop's Q bit for bit.

	// Every operand this hop is not entered on, as the constant the inverse
	// sees on cycle 0: the one still wired there, or the clone's start value.
	auto invert_others = [&](int i) {
		dict<IdString, Const> others;
		ChainStep &step = chain[i];
		for (auto port : data_inputs(step.cell)) {
			if (port == step.port)
				continue;
			int len = GetSize(step.cell->getPort(port));
			others[port] = clone_ports[i].count(port)
					? clone_start(step.cell, step.port, port, len)
					: sigmap(step.cell->getPort(port)).as_const();
		}
		return others;
	};

	StoredValues stored;
	stored.collect(ff, [&](FoldKind kind, Const start, Const &result) {
		if (start.is_fully_undef())
			return false;
		if (!start.is_fully_def())
			refuse("Flop %s cannot move because its %s value is only partly "
					"defined, so the inverse fold would be ambiguous.\n",
					log_id(flop), fold_kind_name(kind));
		Const cur = start;
		for (int i = 0; i < GetSize(chain); i++)
			cur = invert_step(chain[i].cell, chain[i].port, cur, invert_others(i));
		result = cur;
		return true;
	});

	pool<SigBit> forbidden = wire_bits(sigmap(d));
	insert_wire_bits(forbidden, sigmap(q));
	insert_wire_bits(forbidden, sigmap(path_in));
	for (int i = 0; i < GetSize(chain); i++)
		for (auto port : clone_ports[i])
			insert_wire_bits(forbidden, sigmap(chain[i].cell->getPort(port)));
	check_controls(ff, sigmap, forbidden);

	// Last refusal is behind us, so this is the line a dry run stops at.
	if (dry_run)
		return;

	// The move leaves the chain computing the value one cycle later than it did,
	// which is what the path wants and what every other reader of a hop does
	// not. Those readers get a duplicate of the hop that still computes the
	// undelayed value. A duplicate's path operand is the undelayed output of
	// the hop below, so duplication runs from the first hop read off the path
	// all the way down to the cut, whose path input is the one net the move
	// leaves in place. Its other operands are the nets the originals read
	// before the clones went in, which is why this runs first.
	//
	// This is the backward answer to the leftover copy a forward move leaves
	// for extra readers of Q, and it costs more: what has extra readers here is
	// a combinational cell, so the copy is logic rather than a register.
	dict<Cell *, SigSpec> dup_y;
	int ndup = 0;
	for (int i = GetSize(chain) - 1; i >= dup_from; i--) {
		Cell *cell = chain[i].cell;
		SigSpec y = cell->getPort(ID::Y);
		Cell *copy = module->addCell(module->uniquify(cell->name.str() + "_dup"), cell);
		if (i + 1 < GetSize(chain))
			copy->setPort(chain[i].port, dup_y.at(chain[i + 1].cell));

		if (extra[i].output) {
			// A module output has no port to point at the duplicate, so this
			// hop hands the duplicate its original net and takes a fresh one
			// for the delayed value. Everything else reading the hop off the
			// path comes along for free, already on the net the duplicate now
			// drives. Only the path has to be told where the value went: the
			// hop below reads it on its path port, and at the first hop it is
			// what the register's Q becomes, which `link` picks up below.
			copy->setPort(ID::Y, y);
			dup_y[cell] = y;
			if (i > 0) {
				SigSpec ywire = module->addWire(
						module->uniquify(cell->name.str() + "_retimed_y"), GetSize(y));
				cell->setPort(ID::Y, ywire);
				chain[i - 1].cell->setPort(chain[i - 1].port, ywire);
			}
		} else {
			SigSpec ywire = module->addWire(
					module->uniquify(cell->name.str() + "_dup_y"), GetSize(y));
			copy->setPort(ID::Y, ywire);
			dup_y[cell] = ywire;

			dict<SigBit, SigBit> subst;
			SigSpec mapped = sigmap(y);
			for (int b = 0; b < GetSize(mapped); b++)
				subst[mapped[b]] = ywire[b];
			for (auto &rd : extra[i].readers) {
				SigSpec neu;
				for (auto bit : rd.cell->getPort(rd.port)) {
					auto it = subst.find(sigmap(bit));
					neu.append(it == subst.end() ? bit : it->second);
				}
				rd.cell->setPort(rd.port, neu);
			}
		}
		if (extra[i].output)
			log("Duplicating cell %s as %s to keep driving the module output on "
					"the before-path of flop %s.\n", log_id(cell), log_id(copy),
					log_id(flop));
		else if (!extra[i].empty())
			log("Duplicating cell %s as %s for %d reader(s) off the before-path "
					"of flop %s.\n", log_id(cell), log_id(copy),
					GetSize(extra[i].readers), log_id(flop));
		else
			log("Duplicating cell %s as %s to feed the duplicate above it.\n",
					log_id(cell), log_id(copy));
		ndup++;
	}

	int nclone = 0;
	for (int i = 0; i < GetSize(chain); i++) {
		Cell *cell = chain[i].cell;
		for (auto port : clone_ports[i]) {
			SigSpec din = cell->getPort(port);
			int n = GetSize(din);
			// The cut is the cell the command named, so its clones are named
			// for the flop and the port alone. A clone on a hop further down
			// the chain names the cell as well, since several hops of a mux
			// tree all clone a port called S.
			std::string base = flop->name.str() + "_";
			if (cell != cut)
				base += RTLIL::unescape_id(cell->name) + "_";
			base += RTLIL::unescape_id(port);
			SigSpec qwire = module->addWire(module->uniquify(base + "_q"), n);
			FfData cloned = ff;
			cloned.cell = nullptr;
			cloned.name = module->uniquify(base);
			cloned.sig_d = din;
			cloned.sig_q = qwire;
			cloned.width = n;
			Const start = clone_start(cell, chain[i].port, port, n);
			cloned.val_init = stored.got_init ? start : Const(State::Sx, n);
			if (cloned.has_srst)
				cloned.val_srst = stored.got_srst ? start : Const(State::Sx, n);
			if (cloned.has_arst)
				cloned.val_arst = stored.got_arst ? start : Const(State::Sx, n);
			if (cloned.has_aload && cloned.sig_ad.is_fully_const())
				cloned.sig_ad = stored.got_aload ? start : Const(State::Sx, n);
			// Not a refusal, and deliberately fatal. FfData::emit only declines
			// to build a cell for a zero width or for a register left with no
			// control input at all, neither of which can reach here: the width
			// comes from a real port and has_clk was required up front. It also
			// removes the old cell before it can decline, so there is nothing
			// to hand back to a caller even if this were a legality question.
			if (!cloned.emit())
				log_error("Clone of flop %s onto input %s of %s did not "
						"survive being built.\n",
						log_id(flop), log_id(port), log_id(cell));
			cell->setPort(port, qwire);
			log("Cloning flop %s as %s onto input %s of %s.\n",
					log_id(flop), log_id(cloned.name), log_id(port), log_id(cell));
			nclone++;
		}
	}

	// The chain keeps its internal wiring. The flop samples the cut's old
	// path input; the cut reads Q; the cell that used to drive D now drives
	// the old Q sinks. The old D net is reused as the Q / cut-input link,
	// being free once the first hop's Y moves onto the old Q net -- unless
	// that net is a module output, in which case the duplicate above kept it
	// and the link has to be a fresh one. Extra live inputs already hold a
	// clone of that flop.
	SigSpec link = d;
	if (extra.front().output)
		link = module->addWire(
				module->uniquify(flop->name.str() + "_retimed"), GetSize(d));
	front->setPort(ID::Y, q);
	cut->setPort(path_port, link);

	// What the move is not taking goes back as its own cell, and the shared one
	// goes away. This runs before the moved register is built because that one
	// is taking the shared cell's name, which is not free until it is gone. The
	// snapshot the remainder is cut from was taken before any rewiring, and the
	// rewiring above touched only nets this move owns -- the front hop's Y is
	// the moved run's D in full, or the chain walk would not have accepted it --
	// so the other registers come back reading what they always read.
	if (sliced) {
		std::vector<int> rest = other_bits(bits, whole.width);
		FfData keep = whole.slice(rest);
		keep.name = module->uniquify(whole.name.str() + "_rest");
		whole.remove();
		// Fatal rather than refused, for the same reason as the clone above:
		// the shared cell is already gone by the time this could decline.
		if (!keep.emit())
			log_error("The %d register(s) left beside flop %s did not survive "
					"being rebuilt after the move.\n",
					GetSize(rest), log_id(whole.name));
		log("Flop %s held several registers; moving the %d bit(s) whose "
				"before-path reaches %s and leaving the other %d as %s.\n",
				log_id(whole.name), GetSize(bits), log_id(cut), GetSize(rest),
				log_id(keep.name));
	}

	ff.remove_init();
	IdString flop_name = ff.name;
	ff.sig_d = path_in;
	ff.sig_q = link;
	ff.width = GetSize(path_in);
	stored.apply(ff, GetSize(path_in));
	// Fatal rather than refused, for the same reason as the clone above: emit
	// removes the old cell before it can decline to build the new one.
	if (!ff.emit())
		log_error("Flop %s did not survive being rebuilt after the move.\n",
				log_id(flop_name));

	stored.log_folds(flop_name);

	if (nclone)
		log("Retimed %s backward across %d cell(s) ending at %s, cloning %d flop(s).\n",
				log_id(flop_name), GetSize(chain), log_id(cut), nclone);
	else
		log("Retimed %s backward across %d cell(s) ending at %s.\n",
				log_id(flop_name), GetSize(chain), log_id(cut));
	if (ndup)
		log("Duplicated %d chain cell(s) for readers off the before-path.\n", ndup);
}

// Registers capturing the same net as flop, which is what -all-fanouts widens
// the move to. Sharing the D net is what makes them the same move rather than
// merely related ones: the chain back to the cut is fixed by the net, so every
// sibling crosses the same cells for the same reasons, and the only thing left
// to differ is what each register does with the value once it has it.
std::vector<Cell *> capture_siblings(Module *module, SigMap &sigmap, Cell *flop)
{
	SigSpec d = sigmap(flop->getPort(ID::D));
	std::vector<Cell *> out;
	for (auto cell : module->cells()) {
		if (cell == flop || !cell->is_builtin_ff())
			continue;
		if (!cell->hasPort(ID::D) || !cell->hasPort(ID::Q))
			continue;
		if (sigmap(cell->getPort(ID::D)) == d)
			out.push_back(cell);
	}
	return out;
}

// The cell as far back from this register's D as the cut is from the named
// flop's. Every move duplicates the chain for the registers that have not gone
// yet, so a sibling's cut is a copy the pass named itself and there is no name
// to pass down. What does survive the batch is the shape, since the siblings
// all started on one net, so the cut is found by counting hops.
Cell *cut_at_depth(Module *module, Cell *flop, int depth)
{
	SigMap sigmap(module);
	dict<SigBit, BitSrc> drivers = index_output_bits(module, sigmap);
	SigSpec cur = sigmap(flop->getPort(ID::D));
	Cell *cell = nullptr;
	for (int i = 0; i < depth; i++) {
		IdString y_port;
		cell = unique_full_driver(drivers, sigmap, cur, y_port);
		if (cell == nullptr || y_port != ID::Y)
			refuse("The before-path of flop %s is not a unique cell Y at %s.\n",
					log_id(flop), log_signal(cur));
		if (i + 1 < depth)
			cur = sigmap(cell->getPort(
					backward_path_port(sigmap, drivers, cell, flop)));
	}
	return cell;
}

// One backward move per register capturing the cut's output, instead of the one
// the command named. The registers differ in their control signals - that is
// the whole reason they are separate registers - so they cannot be merged into
// one move, and each gets its own copy of the chain. The area that costs is the
// point: the alternative is that the shared cell pins all of them in place.
void apply_backward_all_fanouts(Module *module, Cell *flop, Cell *cut)
{
	if (!flop->is_builtin_ff() || !flop->hasPort(ID::D))
		refuse("Cell %s is not a built-in flip-flop.\n", log_id(flop));

	SigMap sigmap(module);

	// A plain -backward takes one register out of a cell holding several. Here
	// the siblings are found by the net they capture, and a sliced register
	// captures part of one, so what counts as a sibling would have to be settled
	// first. Refused plainly rather than half-answered.
	refuse_if_shared(flop, "-all-fanouts");

	std::vector<Cell *> targets;
	targets.push_back(flop);
	for (auto cell : capture_siblings(module, sigmap, flop))
		targets.push_back(cell);

	// The moves are applied one after another, so a refusal partway through
	// would strand the ones already made with no way back to the module the
	// script handed over. So every move is asked before any of it is made, and
	// the batch is declined whole on the first no.
	//
	// A sibling is asked about the cut the command named rather than about the
	// copy it will really cross, because the copy does not exist yet. The two
	// give the same answer: a copy is the same cells wired to the same operands,
	// and what a sibling could refuse over - its own controls, the values it
	// stores, where it reads the chain besides on D - it refuses over either
	// way. The named flop goes first so that a design where it cannot move says
	// so plainly instead of blaming a sibling.
	apply_backward_move(module, flop, cut, true);
	for (auto cell : targets) {
		if (cell == flop)
			continue;
		try {
			apply_backward_move(module, cell, cut, true);
		} catch (const MoveRefused &refused) {
			refuse("-all-fanouts would have to move register %s, which captures "
					"the same net as flop %s, and cannot: %s",
					log_id(cell), log_id(flop), refused.reason.c_str());
		}
	}

	dict<SigBit, BitSrc> drivers = index_output_bits(module, sigmap);
	std::vector<OffPath> extra;
	int depth = GetSize(collect_backward_chain(module, sigmap, drivers, flop,
			flop->getPort(ID::D), cut, extra));

	// Names and nets to report at the end, read now because the registers are
	// rebuilt rather than edited and the cells these point at will be gone.
	std::string net = log_signal(sigmap(flop->getPort(ID::D)));
	IdString cut_name = cut->name;
	std::vector<IdString> names;
	for (auto cell : targets)
		names.push_back(cell->name);

	apply_backward_move(module, flop, cut);
	for (int i = 1; i < GetSize(targets); i++) {
		try {
			apply_backward_move(module, targets[i],
					cut_at_depth(module, targets[i], depth));
		} catch (const MoveRefused &refused) {
			// Past the first move this is not a legality question any more.
			// There is no untouched module left to answer it with, so a refusal
			// here is fatal rather than something the caller can carry on from.
			// The preflight above is what keeps it from happening; reaching it
			// means the preflight missed something.
			log_error("-all-fanouts moved %d of %d register(s) and then could "
					"not move %s: %s", i, GetSize(targets),
					log_id(names[i]), refused.reason.c_str());
		}
	}

	log("Retimed %d register(s) capturing %s backward across %d cell(s) ending "
			"at %s.\n", GetSize(targets), net.c_str(), depth, log_id(cut_name));
}

void apply_forward_move(Module *module, Cell *flop, Cell *cut)
{
	if (!flop->is_builtin_ff())
		refuse("Cell %s is not a built-in flip-flop.\n", log_id(flop));
	if (data_inputs(cut).empty())
		refuse("Cut cell %s has type %s, which opt_retime cannot move across yet.\n",
				log_id(cut), log_id(cut->type));
	if (flop == cut)
		refuse("Flop and cut must be different cells.\n");

	// A backward move picks the register out of a shared cell by asking which
	// run of D reaches the cut. Forward has no such question to ask: it starts
	// at Q, and the registers in a shared cell fan out to unrelated places, so
	// which one was meant is not written anywhere the pass can read.
	refuse_if_shared(flop, "-forward");

	SigMap sigmap(module);
	FfInitVals initvals(&sigmap, module);

	FfData ff(&initvals, flop);
	if (!ff.has_clk || !flop->hasPort(ID::D) || !flop->hasPort(ID::Q))
		refuse("Cell %s is not a clocked flop with D and Q.\n", log_id(flop));

	dict<SigBit, BitSrc> drivers = index_output_bits(module, sigmap);
	std::vector<ChainStep> chain = collect_chain(module, sigmap, drivers, initvals, ff, flop, cut);

	check_chain(ff, flop, chain);

	// Extra readers of an intermediate Y are not the two-full-hop case
	// next_on_path already refuses. A module output, another flop, or a
	// partial tap still sees that net, and the rewrite would switch the hop
	// from Q to D, so those readers would see the value a cycle early. The
	// cut is exempt: its Y becomes the moved flop's Q. Extra readers of Q
	// itself are peel, below.
	for (int i = 0; i + 1 < GetSize(chain); i++) {
		std::vector<CellPort> others;
		bool drives_output = false;
		scan_extra_readers(module, sigmap, sigmap(chain[i].cell->getPort(ID::Y)),
				chain[i + 1].cell, chain[i + 1].port, others, drives_output);
		if (drives_output || !others.empty())
			refuse("Y of cell %s is read off the after-path of flop %s, so a "
					"forward move past it would change those readers.\n",
					log_id(chain[i].cell), log_id(flop));
	}

	ChainStep first_step = chain.front();
	Cell *first = first_step.cell;
	Cell *last = chain.back().cell;

	SigSpec d = flop->getPort(ID::D);
	SigSpec q = flop->getPort(ID::Q);
	SigSpec y = last->getPort(ID::Y);

	SigSpec map_q = sigmap(q);
	SigSpec map_y = sigmap(y);
	SigSpec map_d = sigmap(d);

	// A slice of Q into the cut is not "other readers": that is the path. Peel
	// only when something besides first_step.port still reads Q, including a
	// module output.
	bool peel = has_other_readers(module, sigmap, map_q, first, first_step.port);

	// A leftover copy keeps the original D. If that D sits on the after-path
	// of the cut, rewriting the cut would change the copy's input, so the
	// extra readers would not keep seeing the original register. Checked
	// before merges so a loop with an observe tap fails for that reason
	// rather than whatever the other operand happens to look like.
	if (peel && signal_reaches(module, sigmap, map_y, map_d))
		refuse("Flop %s cannot move across %s: other readers need a copy left "
				"behind, but the flop's D depends on the cut, so that copy would "
				"not keep its original input.\n",
				log_id(flop), log_id(cut));

	std::vector<Merge> merges = collect_merges(module, sigmap, drivers, initvals, flop, ff, chain);

	// Every stored value the register carries is folded through the chain
	// before anything is rewired, while the merged registers are still around
	// to read their copies from.
	StoredValues stored;
	stored.collect(ff, [&](FoldKind kind, Const start, Const &result) {
		return fold_through(module, sigmap, drivers, initvals, ff, flop, chain,
				kind, start, result);
	});

	// TODO relax some of these contraints by rewiring these control nets
	pool<SigBit> forbidden = wire_bits(map_y);
	if (!peel)
		insert_wire_bits(forbidden, map_q);
	for (auto &merge : merges) {
		if (merge.keep)
			continue;
		insert_wire_bits(forbidden, sigmap(merge.flop->getPort(ID::Q)));
	}

	// TODO relax control checks
	check_controls(ff, sigmap, forbidden);

	// Last thing checked before anything is rewritten. A fine cell is one bit
	// wide with no width parameter to grow, so a cut whose output is a
	// different size has nowhere to put the result. The natural place for this
	// is the resize below, but by then a peeled copy has been added to the
	// module, and a refusal has no way to take it back out.
	if (GetSize(y) != GetSize(q) && ff.is_fine)
		refuse("Flop %s is a single-bit cell and cannot widen to %d bits.\n",
				log_id(flop), GetSize(y));

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
		log("Resizing flop %s from %d to %d bits.\n", log_id(flop), GetSize(q), GetSize(y));
		link = module->addWire(module->uniquify(flop->name.str() + "_retimed"), GetSize(y));
	} else if (peel) {
		link = module->addWire(module->uniquify(flop->name.str() + "_retimed"), GetSize(y));
	}

	// Capture each step's after-path before any port is rewritten; SigMap is
	// a snapshot of the connections as they stood at the start of the move.
	std::vector<SigSpec> paths;
	paths.push_back(map_q);
	for (int i = 0; i + 1 < GetSize(chain); i++)
		paths.push_back(sigmap(chain[i].cell->getPort(ID::Y)));

	for (int i = 0; i < GetSize(chain); i++) {
		ChainStep &step = chain[i];
		SigSpec path = paths[i];
		for (auto port : data_inputs(step.cell)) {
			// Asked with the error flag off, unlike the identical pass
			// collect_merges made over this same chain and port list before
			// any of this ran. Anything worth refusing was refused there, so
			// a failure here is a broken invariant rather than an illegal
			// move, and has to read as one: the rewrite is already under way
			// and a refusal would have nothing to return to.
			std::vector<PortBit> desc;
			bool described = port == step.port
					? describe_port(sigmap, drivers, initvals, ff, flop, step.cell,
							port, path, desc, false)
					: describe_operand(sigmap, drivers, initvals, ff, flop, step.cell,
							port, desc, false);
			log_assert(described);
			SigSpec neu;
			for (auto &bit : desc) {
				if (bit.kind == PortBit::Path)
					neu.append(i == 0 ? d[bit.path_offset] : path[bit.path_offset]);
				else if (bit.kind == PortBit::Flop)
					neu.append(bit.flop->getPort(ID::D)[bit.q_offset]);
				else
					neu.append(SigBit(bit.st));
			}
			step.cell->setPort(port, neu);
		}
	}
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
	// move leaves behind. Extra readers keep their flop; the cut was already
	// rewired to D above.
	int kept = 0;
	for (auto &merge : merges) {
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
	stored.apply(ff, GetSize(y));
	// Fatal rather than refused, for the same reason as the clone above: emit
	// removes the old cell before it can decline to build the new one.
	if (!ff.emit())
		log_error("Flop %s did not survive being rebuilt after the move.\n",
				log_id(flop_name));

	stored.log_folds(flop_name);

	log("Retimed %s forward across %d cell(s) ending at %s, merging %d flop(s).\n",
			log_id(flop_name), GetSize(chain), log_id(cut), GetSize(merges));
	if (kept)
		log("Kept %d merged flop(s) that still have other readers.\n", kept);
}

// Make a move if it is legal, and say why not if it is not. An empty string
// means the move was made; anything else is the reason, ready to print, and
// the module is untouched.
//
// This is the entry point anything driving the pass should use. Picking moves
// automatically means proposing ones that turn out to be illegal, and the
// answer to an illegal proposal has to be "no" rather than the end of the
// script.
template <typename Apply>
std::string try_move(Apply apply)
{
	try {
		apply();
	} catch (const MoveRefused &refused) {
		return refused.reason;
	}
	return "";
}

struct OptRetimePass : public Pass {
	OptRetimePass() : Pass("opt_retime", "retime sequential circuits") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_retime -flop <cell> -cut <cell> -forward|-backward [selection]\n");
		log("\n");
		log("Move one register across a combinational chain, or with -all-fanouts\n");
		log("every register capturing the same net.\n");
		log("\n");
		log("    -flop <cell>\n");
		log("        register to move.\n");
		log("\n");
		log("    -cut <cell>\n");
		log("        cell the flop moves across. Cells between flop and cut move\n");
		log("        with it. The path must be a unique chain. Every data input\n");
		log("        of the cut (select and shift amount included) must be\n");
		log("        registered or constant. Word-level types only: $buf, $not,\n");
		log("        $pos, $neg, $slice, $concat, $add/$sub/$mul/$div/$mod/\n");
		log("        $divfloor/$modfloor/$pow, $and/$or/$xor/$xnor,\n");
		log("        $logic_and/$logic_or/$logic_not, $shl/$sshl/$shr/$sshr/\n");
		log("        $shift/$shiftx, $eq/$ne/$eqx/$nex/$lt/$le/$gt/$ge,\n");
		log("        $reduce_*, $mux/$pmux/$bwmux/$bmux/$demux.\n");
		log("\n");
		log("    -forward\n");
		log("        move the register downstream past -cut. Other operand\n");
		log("        registers are merged in (same clock, enable, and reset net).\n");
		log("        The flop keeps its name and takes the cut's output width.\n");
		log("        Extra readers of an intermediate Y refuse; extra readers of\n");
		log("        the cut Y become the new flop Q.\n");
		log("\n");
		log("    -backward\n");
		log("        move the register upstream onto the path input of -cut.\n");
		log("        A cell holding several registers, as an RTL array leaves\n");
		log("        behind, is taken apart first: the run of D reaching -cut is\n");
		log("        moved under the cell's name and the rest stays beside it.\n");
		log("        Invertible cuts: $buf, $not, $xor, $xnor, $add, $sub, $mul,\n");
		log("        $and, $or, $mux. Other live data inputs get a clone of the flop.\n");
		log("        The moved flop feeds the cut, so its init has to be a\n");
		log("        cut-input that yields the old Q. Types with no such input\n");
		log("        ($mul of an even constant by an odd stored value), or that\n");
		log("        also change width ($eq, $reduce_*), cannot.\n");
		log("\n");
		log("    -all-fanouts\n");
		log("        with -backward, move every register capturing the same net.\n");
		log("        All-or-nothing. No -forward form.\n");
		log("\n");
		log("A refused move is reported and leaves the design unchanged.\n");
		log("Scratchpad: opt_retime.moved, opt_retime.refusal (unset on\n");
		log("success), and opt.did_something when a move is made.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_RETIME pass.\n");

		std::string flop, cut_cell;
		bool forward = false, backward = false;
		bool all_fanouts = false;

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
			if (args[argidx] == "-all-fanouts") {
				all_fanouts = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (flop.empty())
			log_cmd_error("Missing required -flop <cell> option.\n");
		if (cut_cell.empty())
			log_cmd_error("Missing required -cut <cell> option.\n");
		if (forward && backward)
			log_cmd_error("Cannot use -forward and -backward together.\n");
		if (!forward && !backward)
			log_cmd_error("Missing required -forward or -backward option.\n");
		if (all_fanouts && !backward)
			log_cmd_error("-all-fanouts only applies to -backward moves.\n");

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

		log("Move: module=%s flop=%s direction=%s cut=%s%s\n",
				log_id(module), log_id(flop_cell),
				backward ? "backward" : "forward", log_id(cut),
				all_fanouts ? " all-fanouts" : "");

		std::string refused;
		if (all_fanouts)
			refused = try_move([&] { apply_backward_all_fanouts(module, flop_cell, cut); });
		else if (backward)
			refused = try_move([&] { apply_backward_move(module, flop_cell, cut); });
		else
			refused = try_move([&] { apply_forward_move(module, flop_cell, cut); });

		// What happened, for a caller that cannot read the log: opt_retime.moved
		// is the answer and opt_retime.refusal is the reason when it is false.
		// The reason is unset rather than emptied on success, so that a stale
		// one left by an earlier call cannot be read as belonging to this one.
		// Trailing newline trimmed, which the log wants and a scratchpad
		// comparison does not.
		design->scratchpad_set_bool("opt_retime.moved", refused.empty());
		if (refused.empty()) {
			design->scratchpad_unset("opt_retime.refusal");
			// The convention opt and its passes drive their fixpoint loop on.
			design->scratchpad_set_bool("opt.did_something", true);
			return;
		}
		std::string reason = refused;
		while (!reason.empty() && reason.back() == '\n')
			reason.pop_back();
		design->scratchpad_set_string("opt_retime.refusal", reason);

		// Same as the other opt_* passes: an illegal hop is a skip, not a
		// command error. The reason is the answer and the script keeps going
		// with the design as it was.
		log("Refused: %s", refused.c_str());
	}
} OptRetimePass;

PRIVATE_NAMESPACE_END
