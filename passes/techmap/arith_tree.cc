/**
 * Replaces chains of $add/$sub/$alu and $macc cells with carry-save compression trees
 *
 * Terminology:
 * - parent:    Cells that consume another cell's output
 * - chainable: Adds/subs with no carry-out usage
 * - chain:     Connected path of chainable cells
 */

#include "kernel/compressor_tree.h"
#include "kernel/macc.h"
#include "kernel/newcelltypes.h"
#include "kernel/sigtools.h"
#include "kernel/yosys.h"

#include <queue>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ArithTreeOptions {
	CompressorTree::Strategy strategy = CompressorTree::Strategy::PREFER_42;
	CompressorTree::FinalMode final_mode = CompressorTree::FinalMode::RIPPLE;
	bool fma_fusion = true;
	// A compressor level costs roughly fixed depth at any width, so
	// compression only pays when it removes a wide carry-propagate adder.
	int min_width = 0;
	// Hold late operands out of the tree until the level they arrive at
	bool schedule_arrival = false;
	// Place links and leaf operands at the column they enter the sum at, rather
	// than requiring every one of them to start at the result's LSB
	bool bit_offsets = false;
	// Chain a difference whose consumer sign-extends it by copying its MSB
	bool sext_links = false;
	// Schedule at a library full adder's depths (see CompressorTree::fa_depths)
	bool cell_fa = false;
	// Expand a product a chain is the only reader of into the chain's own tree
	bool fma_chains = false;
};

// Widen each adder back over the low bits opt_expr stripped from it, so the adder feeding it has one reader
static void rejoin_stripped_lsbs(Module *module)
{
	SigMap sigmap(module);
	dict<SigBit, std::pair<Cell *, int>> sum_bit;
	pool<Cell *> rejoined;
	auto index = [&](Cell *cell) {
		SigSpec y = sigmap(cell->getPort(ID::Y));
		for (int i = 0; i < GetSize(y); i++)
			sum_bit[y[i]] = {cell, i};
	};
	for (auto cell : module->cells())
		if (cell->type.in(ID($add), ID($sub)))
			index(cell);

	for (auto parent : module->cells()) {
		if (!parent->type.in(ID($add), ID($sub)) || parent->getParam(ID::A_SIGNED).as_bool())
			continue;
		for (auto port : {ID::A, ID::B}) {
			// A subtrahend's low bits would come out negated, so only widen over a minuend
			if (port == ID::B && parent->type == ID($sub))
				continue;
			// The port must start with the child's sum above bits it no longer covers
			SigSpec x = sigmap(parent->getPort(port));
			if (x.empty() || !sum_bit.count(x[0]))
				continue;
			auto [child, k] = sum_bit.at(x[0]);
			SigSpec y = child->getPort(ID::Y);
			if (k == 0 || rejoined.count(child) || GetSize(x) < GetSize(y) - k ||
			    x.extract(0, GetSize(y) - k) != sigmap(y.extract_end(k)))
				continue;
			// A parent that also reads those low bits would end up reading its own sum
			pool<SigBit> reads = sigmap(SigSpec({parent->getPort(ID::A), parent->getPort(ID::B)})).to_sigbit_pool();
			if (!sigmap(y.extract(0, k)).extract(reads).empty())
				continue;

			// Adding zeros below the other operand passes the child's low bits through the parent's sum
			IdString other = port == ID::A ? ID::B : ID::A;
			Wire *wire = module->addWire(NEW_ID, k);
			child->setPort(ID::Y, {y.extract_end(k), wire});
			parent->setPort(port, {parent->getPort(port), wire});
			parent->setPort(other, {parent->getPort(other), SigSpec(State::S0, k)});
			parent->setPort(ID::Y, {parent->getPort(ID::Y), y.extract(0, k)});
			parent->fixup_parameters();
			rejoined.insert(child);
			index(child);
			index(parent);
			break;
		}
	}
}

struct ArithTreeWorker {
	const ArithTreeOptions &opt;
	Module *module;
	SigMap sigmap;

	dict<SigBit, pool<Cell *>> bit_consumers;
	dict<SigBit, int> fanout;
	dict<SigBit, Cell *> bit_driver;
	dict<SigBit, int> arrival_cache;
	dict<Cell *, uint64_t> bound_cache;
	pool<Cell *> arrival_visiting;

	pool<Cell *> addsub;
	pool<Cell *> alu;
	pool<Cell *> macc;
	pool<Cell *> sext_linked;
	pool<Cell *> fused;
	// SILIMATE: final adders built under -final prefix-cmos, and those kept as an AND/OR
	// prefix network because a late product reaches them past the tree
	int prefix_cmos = 0, prefix_kept = 0;

	struct Operand {
		SigSpec sig;
		bool is_signed;
		bool negate;
		// With FMA, when both factors are set, the operand represents a product to
		// be expanded into partial products at extraction time, is_signed then
		// applies to factor_a, and factor_b carries its own signedness
		SigSpec factor_b; // empty for regular operands
		bool factor_b_signed = false;
		// Column the operand's LSB lands in, i.e. it contributes value << offset
		int offset = 0;
	};

	ArithTreeWorker(const ArithTreeOptions &opt, Module *module) : opt(opt), module(module), sigmap(module)
	{
		// Build traversal data
		for (auto cell : module->cells()) {
			for (auto &[name, sig] : cell->connections()) {
				if (cell->input(name)) {
					for (auto bit : sigmap(sig)) {
						bit_consumers[bit].insert(cell);
					}
				}
				if (cell->output(name))
					for (auto bit : sigmap(sig))
						bit_driver[bit] = cell;
			}
		}

		for (auto &[sig, consumers] : bit_consumers)
			fanout[sig] = consumers.size();

		for (auto wire : module->wires())
			if (wire->port_output)
				for (auto bit : sigmap(SigSpec(wire)))
					fanout[bit]++;

		// Collect cell data
		for (auto cell : module->cells()) {
			if (is_addsub(cell))
				addsub.insert(cell);
			else if (is_alu(cell))
				alu.insert(cell);
			else if (is_macc(cell))
				macc.insert(cell);
		}
	}

	static int clog2(int n)
	{
		int r = 0;
		while ((1 << r) < n)
			r++;
		return r;
	}

	// Compressor levels a row of `rows` operands takes to reach two
	static int tree_levels(int rows)
	{
		int levels = 0;
		for (double n = rows; n > 2; n = std::ceil(n * 2.0 / 3.0))
			levels++;
		return levels;
	}

	// Gate delays across a carry-propagate adder, taken as parallel-prefix since
	// that is what a wide $add lowers to
	static int adder_levels(int width) { return 2 * std::max(1, clog2(width)); }

	// Partial-product rows a $macc reduces, i.e. its addends plus a row per
	// multiplied bit
	static int macc_rows(Cell *cell)
	{
		Macc macc;
		macc.from_cell(cell);
		int rows = 0;
		for (auto &term : macc.terms)
			rows += GetSize(term.in_b) ? std::min(GetSize(term.in_a), GetSize(term.in_b)) : 1;
		return rows;
	}

	// Depth of a cell's own logic in gate delays. Word-level cells survive to the
	// netlist as the network they stand for, so each is costed as that network: a
	// prefix adder is logarithmic in its width, a multiplier is a compressor tree
	// over its rows plus that adder, and a shifter is a mux level per amount bit.
	int cell_levels(Cell *cell)
	{
		auto w = [&](IdString port) { return cell->hasPort(port) ? GetSize(cell->getPort(port)) : 1; };

		if (cell->type.in(ID($add), ID($sub), ID($alu), ID($neg)))
			return adder_levels(w(ID::Y));
		if (cell->type == ID($mul))
			return 2 * tree_levels(std::min(w(ID::A), w(ID::B))) + adder_levels(w(ID::Y));
		if (cell->type.in(ID($macc), ID($macc_v2)))
			return 2 * tree_levels(macc_rows(cell)) + adder_levels(w(ID::Y));
		// Restoring division is a subtract and a select per result bit
		if (cell->type.in(ID($div), ID($mod), ID($divfloor), ID($modfloor)))
			return w(ID::Y) * (adder_levels(w(ID::Y)) + 1);
		if (cell->type.in(ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($shiftx)))
			return std::max(1, w(ID::B));
		if (cell->type.in(ID($lt), ID($le), ID($gt), ID($ge)))
			return adder_levels(std::max(w(ID::A), w(ID::B)));
		if (cell->type.in(ID($eq), ID($ne), ID($eqx), ID($nex)))
			return 1 + clog2(std::max(w(ID::A), w(ID::B)));
		if (cell->type.in(ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool),
				  ID($logic_and), ID($logic_or), ID($logic_not)))
			return 1 + clog2(w(ID::A));
		if (cell->type == ID($pmux))
			return 1 + clog2(w(ID::S));
		if (cell->type == ID($fa))
			return 2;
		return 1; // bitwise logic, muxes, and anything unmodelled
	}

	// State elements end the walk: their outputs are there when the cycle starts
	bool is_start(Cell *cell)
	{
		return StaticCellTypes::Compat::mem_ff(cell->type) || cell->type.in(ID($anyseq), ID($anyconst));
	}

	// Arrival of `bit` in gate delays, memoised across the whole module. The walk
	// is post-order over driver cells on an explicit stack, as a long combinational
	// chain would overflow the native one.
	int arrival(SigBit bit)
	{
		// A cell being walked, its inputs, and the latest arrival among those seen so far
		struct Frame {
			Cell *cell;
			SigSpec inputs;
			int next = 0, in = 0;
		};
		std::vector<Frame> stack;

		// Settle `b` into `out` from the memo or as a start point, or push its driver
		int out = 0;
		auto visit = [&](SigBit b) {
			b = sigmap(b);
			auto cached = arrival_cache.find(b);
			if (cached != arrival_cache.end()) {
				out = cached->second;
				return false;
			}

			auto driven = bit_driver.find(b);
			if (!b.is_wire() || driven == bit_driver.end() || is_start(driven->second)) {
				out = arrival_cache[b] = 0;
				return false;
			}

			// A bit already on the stack is part of a combinational loop, which has no
			// arrival to speak of; treat it as a start point rather than walking it again
			Cell *cell = driven->second;
			if (!arrival_visiting.insert(cell).second) {
				out = 0;
				return false;
			}

			SigSpec inputs;
			for (auto &[name, sig] : cell->connections())
				if (cell->input(name))
					inputs.append(sig);
			stack.push_back({cell, sigmap(inputs)});
			return true;
		};

		visit(bit);
		while (!stack.empty()) {
			Frame &top = stack.back();
			if (top.next < GetSize(top.inputs)) {
				// Descend into the next input's driver unless that input is settled; a
				// push may reallocate the stack, so `top` is not used after one
				if (visit(top.inputs[top.next++]))
					continue;
			} else {
				// With every input in, the cell's outputs arrive its own depth later
				out = top.in + cell_levels(top.cell);
				arrival_visiting.erase(top.cell);
				for (auto &[name, sig] : top.cell->connections())
					if (top.cell->output(name))
						for (auto b : sigmap(sig))
							arrival_cache[b] = out;
				stack.pop_back();
				if (stack.empty())
					break;
			}
			// Fold the settled arrival into the cell waiting on it
			stack.back().in = std::max(stack.back().in, out);
		}
		return out;
	}

	int arrival(const SigSpec &sig)
	{
		int a = 0;
		for (auto bit : sigmap(sig))
			a = std::max(a, arrival(bit));
		return a;
	}

	bool is_addsub(Cell *cell) {
		return cell->type == ID($add) || cell->type == ID($sub);
	}

	bool is_alu(Cell *cell) {
		return cell->type == ID($alu);
	}

	bool is_macc(Cell *cell) {
		return cell->type == ID($macc) || cell->type == ID($macc_v2);
	}

	bool is_sub(Cell *cell) {
		SigSpec bi = sigmap(cell->getPort(ID::BI));
		SigSpec ci = sigmap(cell->getPort(ID::CI));
		return GetSize(bi) == 1 && bi[0] == State::S1 && GetSize(ci) == 1 && ci[0] == State::S1;
	}

	bool is_add(Cell *cell)
	{
		SigSpec bi = sigmap(cell->getPort(ID::BI));
		SigSpec ci = sigmap(cell->getPort(ID::CI));
		return GetSize(bi) == 1 && bi[0] == State::S0 && GetSize(ci) == 1 && ci[0] == State::S0;
	}

	bool is_chainable(Cell *cell)
	{
		if (!(is_add(cell) || is_sub(cell)))
			return false;
		for (auto bit : sigmap(cell->getPort(ID::X)))
			if (fanout.count(bit) && fanout[bit] > 0)
				return false;
		for (auto bit : sigmap(cell->getPort(ID::CO)))
			if (fanout.count(bit) && fanout[bit] > 0)
				return false;
		return true;
	}

	// Bits an unsigned read of `sig` can set, below its constant-zero top
	int value_width(const SigSpec &sig)
	{
		int w = GetSize(sig);
		while (w > 0 && sig[w - 1] == State::S0)
			w--;
		return w;
	}

	// The unsigned sum, product or mux whose low result bits `sig` reads below its
	// constant-zero top, or nullptr
	Cell *bound_driver(const SigSpec &sig_in)
	{
		SigSpec sig = sigmap(sig_in);
		int w = value_width(sig);
		auto d = w ? bit_driver.find(sig[0]) : bit_driver.end();
		if (d == bit_driver.end() || !(d->second->type.in(ID($add), ID($mul), ID($mux)) || (is_alu(d->second) && is_add(d->second))))
			return nullptr;
		SigSpec y = sigmap(d->second->getPort(ID::Y));
		return GetSize(y) >= w && y.extract(0, w) == sig.extract(0, w) ? d->second : nullptr;
	}

	// Largest value an unsigned read of `sig` takes. A low slice of an unsigned sum or
	// product is bounded by that cell's operands, which can be tighter than its width:
	// three terms of 29, 28 and 27 bits fit in 30. UINT64_MAX when nothing below 64
	// bits is known.
	uint64_t value_bound(const SigSpec &sig)
	{
		int w = value_width(sigmap(sig));
		uint64_t full = w >= 64 ? UINT64_MAX : (uint64_t(1) << w) - 1;
		Cell *d = bound_driver(sig);
		auto it = d ? bound_cache.find(d) : bound_cache.end();
		return it == bound_cache.end() ? full : std::min(full, it->second);
	}

	// Largest value an unsigned sum, product or mux computes before its Y truncates it.
	// Its drivers are bounded first off an explicit stack: an add or mux chain would
	// otherwise recurse once per link and overflow the native one. A driver still
	// open closes a combinational loop, so it reads at its width.
	uint64_t cell_bound(Cell *top)
	{
		std::vector<Cell *> todo = {top};
		pool<Cell *> open;
		while (!todo.empty()) {
			Cell *cell = todo.back();
			if (bound_cache.count(cell)) {
				todo.pop_back();
				continue;
			}
			if (open.insert(cell).second) {
				for (auto port : {ID::A, ID::B})
					if (Cell *d = bound_driver(cell->getPort(port)); d && !bound_cache.count(d) && !open.count(d))
						todo.push_back(d);
				continue;
			}
			todo.pop_back();
			uint64_t a = value_bound(cell->getPort(ID::A)), b = value_bound(cell->getPort(ID::B)), r = std::max(a, b);
			if (cell->type != ID($mux)) {
				bool ovf = cell->type == ID($mul) ? __builtin_mul_overflow(a, b, &r) : __builtin_add_overflow(a, b, &r);
				if (ovf || cell->getParam(ID::A_SIGNED).as_bool() || cell->getParam(ID::B_SIGNED).as_bool())
					r = UINT64_MAX;
			}
			bound_cache[cell] = r;
		}
		return bound_cache.at(top);
	}

	// A link truncates its result at its own Y width, so flattening it into a wider
	// consumer is only sound when that truncation provably never fires. This is the
	// same question macc_may_overflow() answers for the structurally identical $macc
	// merge in alumacc, answered from operand widths and, failing that, from the
	// operands' own bounds.
	bool link_may_overflow(Cell *link)
	{
		// Only unsigned addition has a bound this simple. Subtraction borrows below
		// zero and wraps into the discarded bits, and a signed operand changes what
		// those bits mean, so neither is proven here.
		if (!(link->type == ID($add) || (is_alu(link) && is_add(link))))
			return true;
		if (link->getParam(ID::A_SIGNED).as_bool() || link->getParam(ID::B_SIGNED).as_bool())
			return true;

		// a + b never needs more than one bit beyond the wider operand, since
		// (2**wa - 1) + (2**wb - 1) < 2**(max(wa, wb) + 1).
		int wa = GetSize(link->getPort(ID::A)), wb = GetSize(link->getPort(ID::B));
		int need = wb ? std::max(wa, wb) + 1 : wa;
		int yw = GetSize(link->getPort(ID::Y));
		return yw < need && !fits_below(link, yw);
	}

	// Whether an unsigned add's result provably stays under 2**w, leaving its bits
	// from w up always zero
	bool fits_below(Cell *link, int w)
	{
		if (!(link->type == ID($add) || (is_alu(link) && is_add(link))))
			return false;
		uint64_t b = cell_bound(link);
		return b != UINT64_MAX && (w >= 64 || (b >> w) == 0);
	}

	// An unsigned difference with a bit to spare for the borrow is exact read as
	// signed, since a - b lies strictly between -2**wb and 2**wa. wreduce narrows
	// an unsigned $sub to exactly this width and copies the MSB into the bits above.
	bool link_exact_signed(Cell *link)
	{
		if (!(link->type == ID($sub) || (is_alu(link) && is_sub(link))))
			return false;
		if (link->getParam(ID::A_SIGNED).as_bool() || link->getParam(ID::B_SIGNED).as_bool())
			return false;
		int wa = GetSize(link->getPort(ID::A)), wb = GetSize(link->getPort(ID::B));
		return GetSize(link->getPort(ID::Y)) > std::max(wa, wb);
	}

	// Whether `parent` reads `sig` only at `offset` in `port` and as copies of its MSB
	// above it, through the parent's result width
	bool sign_extends(Cell *parent, IdString port, int offset, const SigSpec &sig)
	{
		SigSpec p = sigmap(parent->getPort(port));
		SigSpec other = sigmap(parent->getPort(port == ID::A ? ID::B : ID::A));
		int top = offset + GetSize(sig);
		if (GetSize(p) < GetSize(parent->getPort(ID::Y)) || !p.extract(0, offset).extract(sig).empty() ||
		    !other.extract(sig).empty())
			return false;
		return p.extract_end(top) == SigSpec(sig[GetSize(sig) - 1], GetSize(p) - top);
	}

	// Bit position inside a `parent` port at which a child's live result bits `y`
	// appear, with `port` receiving that port's name. -1 when they are not exactly one
	// ascending run in exactly one port, since then they have no single scale factor.
	// The offset is what makes a partial link exact: the child's sum enters the parent
	// scaled by 2**offset, so every operand of the child does too.
	int link_offset(const SigSpec &y, Cell *parent, IdString &port)
	{
		int n = GetSize(y), offset = -1;
		for (auto name : {ID::A, ID::B}) {
			SigSpec p = sigmap(parent->getPort(name));
			for (int i = 0; i + n <= GetSize(p); i++) {
				if (p[i] != y[0] || p.extract(i, n) != y)
					continue;
				if (offset >= 0)
					return -1;
				offset = i;
				port = name;
			}
		}
		return offset;
	}

	// Whether `sig` is the low bits of one of `parent`'s operand ports with only
	// constant zeros above it, which is the one partial coverage a reading based at
	// the result LSB still gets right: those zeros contribute nothing, so the link
	// keeps weight 1 and hides no operand.
	bool covers_port_low(Cell *parent, const SigSpec &sig, IdString &port)
	{
		for (auto name : {ID::A, ID::B}) {
			SigSpec p = sigmap(parent->getPort(name));
			if (GetSize(p) >= GetSize(sig) && p.extract(0, GetSize(sig)) == sig &&
			    p.extract_end(GetSize(sig)).is_fully_zero()) {
				port = name;
				return true;
			}
		}
		return false;
	}

	Cell *sole_chainable_consumer(Cell *cell, const pool<Cell *> &candidates, int &offset)
	{
		// Top bits a link's bound proves zero may go unread: opt_signif narrows the
		// consumer past them before wreduce trims them, and dropping zeros loses nothing
		SigSpec sig = sigmap(cell->getPort(ID::Y));
		int live = GetSize(sig);
		while (live > 1 && !fanout.count(sig[live - 1]) && fits_below(cell, live - 1))
			live--;
		sig = sig.extract(0, live);
		offset = 0;
		Cell *consumer = nullptr;
		for (auto bit : sig) {
			if (!fanout.count(bit) || fanout[bit] != 1)
				return nullptr;
			if (!bit_consumers.count(bit) || bit_consumers[bit].size() != 1)
				return nullptr;

			Cell *c = *bit_consumers[bit].begin();
			if (!candidates.count(c))
				return nullptr;

			if (consumer == nullptr)
				consumer = c;
			else if (consumer != c)
				return nullptr;
		}
		if (consumer == nullptr)
			return nullptr;

		// Where the link lands in its consumer. A link sitting above its port's LSB is
		// only representable once operands carry a column, so without -bit-offsets it
		// is refused: reading such a port as a value based at the result LSB both
		// misplaces the link's own operands and drops the bits beside it.
		IdString port;
		if (opt.bit_offsets) {
			offset = link_offset(sig, consumer, port);
			if (offset < 0)
				return nullptr;
			// A signed port extends from its own MSB, not from any run inside it, so
			// only a link covering the whole port can be split off one.
			IdString port_signed = (port == ID::A) ? ID::A_SIGNED : ID::B_SIGNED;
			if (GetSize(sigmap(consumer->getPort(port))) != GetSize(sig) &&
			    consumer->getParam(port_signed).as_bool())
				return nullptr;
		} else if (!covers_port_low(consumer, sig, port)) {
			return nullptr;
		}

		// The link's bits anywhere else in the consumer drop out with it, which only MSB
		// copies sign-extending a difference that is exact read as signed survive
		SigSpec rest = sigmap(consumer->getPort(port == ID::A ? ID::B : ID::A));
		SigSpec own = sigmap(consumer->getPort(port));
		own.remove(offset, GetSize(sig));
		rest.append(own);
		bool sext = false;
		if (!rest.extract(sig).empty()) {
			if (!opt.sext_links || !opt.bit_offsets || !sign_extends(consumer, port, offset, sig) ||
			    !link_exact_signed(cell))
				return nullptr;
			sext = true;
			sext_linked.insert(cell);
		}

		// A link whose field stops below its consumer's MSB discards a carry the wider
		// consumer would otherwise see, since (x % 2**link) % 2**parent == x % 2**parent
		// only when parent <= offset + link. Flatten it anyway when the link cannot
		// reach that carry, but only if the consumer zero-extends it: a sign-extended
		// narrow link means something different from the full-width sum that replaces it.
		if (!sext && offset + GetSize(sig) < GetSize(consumer->getPort(ID::Y))) {
			bool consumer_extends_unsigned = !consumer->getParam(ID::A_SIGNED).as_bool() &&
			                                 !consumer->getParam(ID::B_SIGNED).as_bool();
			if (!consumer_extends_unsigned || link_may_overflow(cell))
				return nullptr;
		}
		return consumer;
	}

	dict<Cell *, Cell *> find_parents(const pool<Cell *> &candidates, dict<Cell *, int> &link_off)
	{
		dict<Cell *, Cell *> parent_of;
		for (auto cell : candidates) {
			int offset = 0;
			Cell *consumer = sole_chainable_consumer(cell, candidates, offset);
			if (consumer && consumer != cell) {
				parent_of[cell] = consumer;
				link_off[cell] = offset;
			}
		}
		return parent_of;
	}

	std::pair<dict<Cell *, pool<Cell *>>, pool<Cell *>> invert_parent_map(const dict<Cell *, Cell *> &parent_of)
	{
		dict<Cell *, pool<Cell *>> children_of;
		pool<Cell *> has_parent;
		for (auto &[child, parent] : parent_of) {
			children_of[parent].insert(child);
			has_parent.insert(child);
		}
		return {children_of, has_parent};
	}

	pool<Cell *> collect_chain(Cell *root, const dict<Cell *, pool<Cell *>> &children_of)
	{
		pool<Cell *> chain;
		std::queue<Cell *> q;
		q.push(root);
		while (!q.empty()) {
			Cell *cur = q.front();
			q.pop();
			if (!chain.insert(cur).second)
				continue;
			auto it = children_of.find(cur);
			if (it != children_of.end())
				for (auto child : it->second)
					q.push(child);
		}
		return chain;
	}

	pool<SigBit> internal_bits(const pool<Cell *> &chain)
	{
		pool<SigBit> bits;
		for (auto cell : chain)
			for (auto bit : sigmap(cell->getPort(ID::Y)))
				bits.insert(bit);
		return bits;
	}

	bool overlaps(SigSpec sig, const pool<SigBit> &bits)
	{
		for (auto bit : sig)
			if (bits.count(bit))
				return true;
		return false;
	}

	bool feeds_subtracted_port(Cell *child, Cell *parent)
	{
		bool parent_subtracts;
		if (parent->type == ID($sub))
			parent_subtracts = true;
		else if (is_alu(parent))
			parent_subtracts = is_sub(parent);
		else
			return false;

		if (!parent_subtracts)
			return false;

		SigSpec child_y = sigmap(child->getPort(ID::Y));
		SigSpec parent_b = sigmap(parent->getPort(ID::B));
		for (auto bit : child_y)
			for (auto pbit : parent_b)
				if (bit == pbit)
					return true;
		return false;
	}

	// Negation flag and column of every cell in `chain`, walked down from the root.
	// Columns compose additively: a link at offset k inside a parent that itself sits
	// at column j puts its own operands at j + k.
	void propagate_chain_state(const pool<Cell *> &chain, Cell *root, const dict<Cell *, Cell *> &parent_of,
				   const dict<Cell *, int> &link_off, dict<Cell *, bool> &negated,
				   dict<Cell *, int> &offset_of)
	{
		negated[root] = false;
		offset_of[root] = 0;
		std::queue<Cell *> q;
		q.push(root);
		while (!q.empty()) {
			Cell *cur = q.front();
			q.pop();
			for (auto cell : chain) {
				if (!parent_of.count(cell) || parent_of.at(cell) != cur)
					continue;
				if (negated.count(cell))
					continue;
				negated[cell] = negated[cur] ^ feeds_subtracted_port(cell, cur);
				offset_of[cell] = offset_of[cur] + link_off.at(cell);
				q.push(cell);
			}
		}
	}

	// A run of a product's result bits read at `column`, the column of result bit 0
	struct Piece {
		int bit, len, column;
	};

	// Whether `pieces` read every bit `mul` can set exactly once each, at one column,
	// with nothing else reading the product, so the chain's tree can take it as rows.
	// The bits read must hold the whole product unless the rest lands at or above
	// the top of the `width`-bit sum.
	bool fusable(Cell *mul, std::vector<Piece> &pieces, const dict<SigBit, int> &reads, int width)
	{
		std::sort(pieces.begin(), pieces.end(), [](const Piece &a, const Piece &b) { return a.bit < b.bit; });
		int w = 0;
		for (auto &p : pieces) {
			if (p.bit != w || p.column != pieces[0].column)
				return false;
			w += p.len;
		}
		SigSpec y = sigmap(mul->getPort(ID::Y));
		for (int i = 0; i < GetSize(y); i++)
			if (fanout.count(y[i]) && fanout.at(y[i]) != (i < w ? 1 : 0))
				return false;
		for (int i = 0; i < w; i++)
			if (reads.at(y[i], 0) != 1)
				return false;
		uint64_t b = cell_bound(mul);
		return pieces[0].column + w >= width || (b != UINT64_MAX && (w >= 64 || (b >> w) == 0));
	}

	std::vector<Operand> extract_chain_operands(const pool<Cell *> &chain, Cell *root, const dict<Cell *, Cell *> &parent_of,
						    const dict<Cell *, int> &link_off, std::vector<int> &neg_offsets,
						    pool<Cell *> &chain_fused)
	{
		pool<SigBit> chain_bits = internal_bits(chain);
		int width = GetSize(root->getPort(ID::Y));
		// -fma-chains: unsigned product bits the chain reads, by product; the operands
		// holding them, split once it is known which products fuse; and how often each
		// bit is read, which a product taken as rows has to be read exactly once
		dict<Cell *, std::vector<Piece>> pieces;
		std::vector<int> held;
		dict<SigBit, int> reads;
		if (opt.fma_chains)
			for (auto cell : chain)
				for (auto name : {ID::A, ID::B})
					for (auto bit : sigmap(cell->getPort(name)))
						reads[bit]++;
		dict<Cell *, bool> negated;
		dict<Cell *, int> offset_of;
		propagate_chain_state(chain, root, parent_of, link_off, negated, offset_of);

		// Extract leaf operands
		std::vector<Operand> operands;

		for (auto cell : chain) {
			bool cell_neg = negated.count(cell) ? negated[cell] : false;
			int base = offset_of.count(cell) ? offset_of.at(cell) : 0;
			bool b_sub = (cell->type == ID($sub)) || (is_alu(cell) && is_sub(cell));

			for (auto name : {ID::A, ID::B}) {
				SigSpec port = sigmap(cell->getPort(name));
				bool port_signed = cell->getParam(name == ID::A ? ID::A_SIGNED : ID::B_SIGNED).as_bool();
				bool neg = cell_neg ^ (name == ID::B && b_sub);
				auto take = [&](SigSpec sig, bool is_signed, int offset) {
					// Constant-zero low bits only scale the operand, and
					// -(v << k) == (-v) << k, so move them into the column
					// either way. A product added at a bit offset reaches the
					// sum in exactly that shape.
					while (opt.bit_offsets && GetSize(sig) > 1 && sig[0] == State::S0) {
						sig.remove(0, 1);
						offset++;
					}
					// Note where the unsigned product bits in a run land
					if (opt.fma_chains && !neg && !is_signed) {
						bool any = false;
						for (int i = 0; i < GetSize(sig);) {
							auto d = sig[i].wire ? bit_driver.find(sig[i]) : bit_driver.end();
							Cell *mul = d != bit_driver.end() && d->second->type == ID($mul) &&
									!d->second->getParam(ID::A_SIGNED).as_bool() &&
									!d->second->getParam(ID::B_SIGNED).as_bool() ? d->second : nullptr;
							if (!mul) {
								i++;
								continue;
							}
							SigSpec y = sigmap(mul->getPort(ID::Y));
							int k = 0;
							while (y[k] != sig[i])
								k++;
							int j = i + 1;
							while (j < GetSize(sig) && k + j - i < GetSize(y) && sig[j] == y[k + j - i])
								j++;
							pieces[mul].push_back({k, j - i, offset + i - k});
							i = j;
							any = true;
						}
						if (any)
							held.push_back(GetSize(operands));
					}
					operands.push_back({sig, is_signed, neg, SigSpec(), false, offset});
					if (neg)
						neg_offsets.push_back(offset);
				};

				// A signed port extends from its own MSB, so its runs are not
				// independent columns; the link rules keep such a port either
				// whole or entirely covered by one link.
				if (port_signed || !opt.bit_offsets) {
					if (!overlaps(port, chain_bits))
						take(port, port_signed, base);
					continue;
				}

				// Split the port into maximal runs of bits no chain cell drives.
				// The runs a chain cell does drive are links, already accounted
				// for by the cells they come from, so a port mixing a link with
				// leaf bits contributes only the leaf runs beside it.
				for (int i = 0; i < GetSize(port);) {
					if (chain_bits.count(port[i])) {
						i++;
						continue;
					}
					int j = i + 1;
					while (j < GetSize(port) && !chain_bits.count(port[j]))
						j++;
					take(port.extract(i, j - i), false, base + i);
					i = j;
				}
			}
		}

		// A product read whole enters as its partial-product rows, on the narrower
		// factor's bits, and leaves the runs it was read in; a run otherwise stays whole.
		// That only shortens the sum for a product arriving after everything else it
		// adds: otherwise the later operand still sets the depth and the rows cost area.
		pool<SigBit> taken;
		for (auto &[mul, ps] : pieces)
			if (fusable(mul, ps, reads, width))
				for (auto bit : sigmap(mul->getPort(ID::Y)))
					taken.insert(bit);
		int rest = 0;
		for (auto &op : operands) {
			SigSpec bits;
			for (auto bit : sigmap(op.sig))
				if (!taken.count(bit))
					bits.append(bit);
			rest = std::max(rest, arrival(bits));
		}
		taken.clear();
		for (auto &[mul, ps] : pieces) {
			if (!fusable(mul, ps, reads, width) || arrival(mul->getPort(ID::Y)) <= rest)
				continue;
			SigSpec a = sigmap(mul->getPort(ID::A)), b = sigmap(mul->getPort(ID::B));
			if (GetSize(a) > GetSize(b))
				std::swap(a, b);
			operands.push_back({a, false, false, b, false, ps[0].column});
			chain_fused.insert(mul);
			for (auto bit : sigmap(mul->getPort(ID::Y)))
				taken.insert(bit);
		}
		for (int h = GetSize(held) - 1; h >= 0; h--) {
			Operand op = operands[held[h]];
			if (!overlaps(op.sig, taken))
				continue;
			// The bits between fused products sum to the same at their own columns
			std::vector<Operand> rest;
			for (int i = 0; i < GetSize(op.sig);) {
				int j = i;
				while (j < GetSize(op.sig) && !taken.count(op.sig[j]))
					j++;
				if (j > i)
					rest.push_back({op.sig.extract(i, j - i), false, false, SigSpec(), false, op.offset + i});
				while (j < GetSize(op.sig) && taken.count(op.sig[j]))
					j++;
				i = j;
			}
			operands.erase(operands.begin() + held[h]);
			operands.insert(operands.begin() + held[h], rest.begin(), rest.end());
		}
		return operands;
	}

	bool extract_macc_operands(Cell *cell, std::vector<Operand> &operands, std::vector<int> &neg_offsets)
	{
		Macc macc(cell);

		for (auto &term : macc.terms) {
			if (GetSize(term.in_b) != 0) {
				if (!opt.fma_fusion)
					return false;

				// Preserve term as a multiplicative operand which is expanded into partial products
				Operand op;
				op.sig = term.in_a;
				op.is_signed = term.is_signed;
				op.negate = term.do_subtract;
				op.factor_b = term.in_b;
				op.factor_b_signed = term.is_signed;
				operands.push_back(op);
				continue;
			}
			operands.push_back({term.in_a, term.is_signed, term.do_subtract, SigSpec(), false, 0});
			if (term.do_subtract)
				neg_offsets.push_back(0);
		}
		return true;
	}

	// An operand at column k contributes value << k, i.e. its bits sit that far up
	static SigSpec scale(const SigSpec &sig, int offset)
	{
		if (offset == 0)
			return sig;
		SigSpec scaled(State::S0, offset);
		scaled.append(sig);
		return scaled;
	}

	// Two's complement of an operand at column k is ~value plus 2**k, so the
	// correction row is the sum of those bits rather than a count of negated operands
	static SigSpec neg_correction(const std::vector<int> &offsets, int width)
	{
		std::vector<State> bits(width, State::S0);
		for (int offset : offsets)
			for (int i = offset; i < width; i++) {
				bool carry = (bits[i] == State::S1);
				bits[i] = carry ? State::S0 : State::S1;
				if (!carry)
					break;
			}
		return SigSpec(Const(bits));
	}

	std::vector<CompressorTree::DepthSig> build_operand_pool(Cell *cell, std::vector<Operand> &operands, int width, std::vector<int> &neg_offsets)
	{
		// Expand operands into a flat list of signals for reduction
		std::vector<CompressorTree::DepthSig> pool;
		pool.reserve(operands.size() * 2);
		// -fma-chains: unsigned product rows as the columns they cover, packed below
		struct Row {
			int lo;
			SigSpec bits;
			int depth;
		};
		std::vector<Row> rows;
		IdString cell_name = cell->name;

		for (auto &op : operands) {
			// Columns the operand can still reach; one based at or above the result
			// MSB contributes nothing, and its negation correction cancels too
			int body = width - op.offset;
			if (body <= 0)
				continue;

			if (GetSize(op.factor_b) == 0) {
				// Additive operand
				int depth = arrival(op.sig);
				op.sig.extend_u0(body, op.is_signed);
				if (op.negate) {
					op.sig = module->Not(NEW_ID2_SUFFIX("not"), op.sig); // SILIMATE: Improve the naming
					depth++;
				}
				pool.push_back({scale(op.sig, op.offset), depth});
			} else {
				// Multiplicative operand: every row is one AND past both factors
				int depth = std::max(arrival(op.sig), arrival(op.factor_b)) + 1;
				if (opt.fma_chains && !op.is_signed && !op.factor_b_signed && !op.negate) {
					for (int i = 0; i < GetSize(op.sig) && i < body; i++) {
						int len = std::min(GetSize(op.factor_b), body - i);
						SigSpec bits = module->addWire(NEW_ID3_SUFFIX("pp"), len);
						module->addAnd(NEW_ID3_SUFFIX("pp_and"), op.factor_b.extract(0, len), SigSpec(op.sig[i], len), bits);
						rows.push_back({op.offset + i, bits, depth});
					}
					continue;
				}
				auto pps = CompressorTree::generate_partial_products(module, op.sig, op.factor_b, op.is_signed, op.factor_b_signed, body, cell->name); // SILIMATE: Improve the naming

				if (!op.negate) {
					for (auto &pp : pps)
						pool.push_back({scale(pp.sig, op.offset), depth});
					continue;
				}

				auto [pa, pb] = CompressorTree::reduce_scheduled(module, pps, body, opt.strategy, cell->name, nullptr, nullptr, opt.cell_fa); // SILIMATE: Improve the naming
				SigSpec p = module->addWire(NEW_ID2_SUFFIX("prod"), body); // SILIMATE: Improve the naming
				module->addAdd(NEW_ID2_SUFFIX("add"), pa, pb, p, false); // SILIMATE: Improve the naming
				SigSpec np = module->addWire(NEW_ID2_SUFFIX("nprod"), body); // SILIMATE: Improve the naming
				module->addNot(NEW_ID2_SUFFIX("not"), p, np); // SILIMATE: Improve the naming
				// Its own rows, the adder above, and the inverter
				pool.push_back({scale(np, op.offset), depth + 2 * tree_levels(GetSize(pps)) + adder_levels(body) + 1});
				neg_offsets.push_back(op.offset);
			}
		}

		// Rows that share no column and arrive within a compressor of each other are
		// one row: a hand-split multiply's tiles otherwise each take a row of their
		// own, which the tree pays for in levels the full product would not need
		std::sort(rows.begin(), rows.end(), [](const Row &a, const Row &b) { return a.depth != b.depth ? a.depth < b.depth : a.lo < b.lo; });
		// Rows come in arrival order, so a line's first row is its earliest
		struct Line {
			std::vector<SigBit> bits;
			int first, last;
		};
		std::vector<Line> lines;
		for (auto &r : rows) {
			auto fits = [&](const Line &line) {
				if (r.depth - line.first >= CompressorTree::FA_GATE_DEPTH)
					return false;
				for (int i = 0; i < GetSize(r.bits); i++)
					if (line.bits[r.lo + i] != State::S0)
						return false;
				return true;
			};
			auto line = std::find_if(lines.begin(), lines.end(), fits);
			if (line == lines.end())
				line = lines.insert(lines.end(), {std::vector<SigBit>(width, State::S0), r.depth, r.depth});
			for (int i = 0; i < GetSize(r.bits); i++)
				line->bits[r.lo + i] = r.bits[i];
			line->last = r.depth;
		}
		for (auto &line : lines)
			pool.push_back({SigSpec(line.bits), line.last});

		if (!neg_offsets.empty())
			pool.push_back({neg_correction(neg_offsets, width), 0});

		rebase_depths(pool);
		return pool;
	}

	// Turn arrival estimates into levels the tree can act on. Both sides count gate
	// delays, so the origin moves to the earliest operand, and operands within a
	// compressor of each other share a level: the tree cannot separate them by less
	// than that, and doing so only fragments its groupings for a difference the
	// estimate cannot resolve anyway.
	//
	// Three operands reduce in one level whatever their arrivals, so scheduling
	// them can only reorder one compressor's ports. Bit-level detail decides that
	// -- an operand zero in a column degenerates the compressor there -- and a
	// word-level arrival estimate does not see it, so leave those pools alone.
	void rebase_depths(std::vector<CompressorTree::DepthSig> &pool)
	{
		if (!opt.schedule_arrival || GetSize(pool) <= 3) {
			for (auto &e : pool)
				e.depth = 0;
			return;
		}

		std::vector<int> sorted;
		for (auto &e : pool)
			sorted.push_back(e.depth);
		std::sort(sorted.begin(), sorted.end());

		// Collapse each run of near-equal arrivals onto the earliest of that run
		dict<int, int> level;
		int start = sorted.front();
		for (int d : sorted) {
			if (d - start >= CompressorTree::FA_GATE_DEPTH)
				start = d;
			level[d] = start - sorted.front();
		}
		for (auto &e : pool)
			e.depth = level.at(e.depth);
	}

	// SILIMATE: whether a bit comes out of a word-level multiplier, directly or through a select arm
	bool from_product(SigBit bit)
	{
		auto is_product = [&](SigBit b) {
			auto d = bit_driver.find(sigmap(b));
			return d != bit_driver.end() && d->second->type.in(ID($mul), ID($macc), ID($macc_v2));
		};
		if (is_product(bit))
			return true;
		auto d = bit_driver.find(sigmap(bit));
		if (d == bit_driver.end() || !d->second->type.in(ID($mux), ID($pmux)))
			return false;
		for (auto port : {ID::A, ID::B})
			for (auto arm : d->second->getPort(port))
				if (is_product(arm))
					return true;
		return false;
	}

	// SILIMATE: an inverting-gate prefix adder gives every input full log depth, which suits
	// inputs that arrive together. A late product whose upper bits reach a or b untouched,
	// within a compressor level of the tree's outputs, does better on the AND/OR network
	// the mapper reshapes, with its shorter carry path from the top columns.
	bool late_product_bypass(const SigSpec &a, const SigSpec &b, const dict<SigBit, int> &leaf, int earliest, int final_depth)
	{
		int bar = std::max(earliest + final_depth - CompressorTree::FA_GATE_DEPTH, earliest + CompressorTree::FA_GATE_DEPTH);
		for (int i = 0; i < GetSize(a); i++)
			for (auto bit : {a[i], b[i]}) {
				auto it = leaf.find(bit);
				if (it != leaf.end() && it->second >= bar && from_product(bit))
					return true;
			}
		return false;
	}

	void emit_tree(Cell *cell, std::vector<Operand> &operands, SigSpec result_y, std::vector<int> &neg_offsets)
	{
		int width = GetSize(result_y);
		// SILIMATE: -final prefix-cmos needs the earliest operand's arrival and that of every
		// bit handed to the tree
		bool cmos = opt.final_mode == CompressorTree::FinalMode::PREFIX_CMOS;
		int earliest = -1;
		if (cmos)
			for (auto &op : operands) {
				int d = GetSize(op.factor_b) ? std::max(arrival(op.sig), arrival(op.factor_b)) + 1 : arrival(op.sig);
				earliest = earliest < 0 ? d : std::min(earliest, d);
			}
		auto pool = build_operand_pool(cell, operands, width, neg_offsets);
		dict<SigBit, int> leaf;
		if (cmos)
			for (auto &e : pool)
				for (auto bit : e.sig)
					if (bit.wire)
						leaf[bit] = arrival(bit);
		int final_depth = 0;
		auto [a, b] = CompressorTree::reduce_scheduled(module, std::move(pool), width, opt.strategy, cell->name, nullptr, &final_depth, opt.cell_fa); // SILIMATE: Improve the naming
		auto final_choice = CompressorTree::pick_final_adder(width, final_depth, opt.final_mode);
		if (cmos) {
			if (late_product_bypass(a, b, leaf, std::max(earliest, 0), final_depth)) {
				final_choice = CompressorTree::FinalAdder::PARALLEL_PREFIX;
				prefix_kept++;
			} else {
				prefix_cmos++;
			}
		}
		CompressorTree::emit_final_adder(module, a, b, result_y, final_choice, cell->name); // SILIMATE: Improve the naming
	}

	void process_chains()
	{
		pool<Cell *> candidates;
		for (auto cell : addsub)
			candidates.insert(cell);
		for (auto cell : alu)
			if (is_chainable(cell))
				candidates.insert(cell);

		if (candidates.empty())
			return;

		dict<Cell *, int> link_off;
		auto parent_of = find_parents(candidates, link_off);
		auto [children_of, has_parent] = invert_parent_map(parent_of);

		pool<Cell *> to_remove;
		for (auto root : candidates) {
			if (has_parent.count(root) || to_remove.count(root))
				continue; // Not a tree root

			if (GetSize(root->getPort(ID::Y)) < opt.min_width)
				continue;

			pool<Cell *> chain = collect_chain(root, children_of);
			if (chain.size() < 2)
				continue;

			// Products taken as rows are only gone once the tree replacing them is built
			std::vector<int> neg_offsets;
			pool<Cell *> chain_fused;
			auto operands = extract_chain_operands(chain, root, parent_of, link_off, neg_offsets, chain_fused);
			if (operands.size() < 3 && chain_fused.empty())
				continue;

			// Only -bit-offsets can put an operand above the result LSB, so this
			// counts what the flag actually recovered on this chain
			int weighted = 0;
			for (auto &op : operands)
				if (op.offset != 0)
					weighted++;
			if (weighted)
				log("Reduced %d weighted operand(s) into the tree at %s.\n", weighted, log_id(root));
			int sext = 0;
			for (auto c : chain)
				if (sext_linked.count(c))
					sext++;
			if (sext)
				log("Chained %d sign-extended difference(s) into the tree at %s.\n", sext, log_id(root));

			for (auto c : chain)
				to_remove.insert(c);

			emit_tree(root, operands, root->getPort(ID::Y), neg_offsets);
			for (auto mul : chain_fused)
				fused.insert(mul);
		}

		if (!fused.empty())
			log("Expanded %d product(s) into the trees of the chains reading them.\n", GetSize(fused));
		for (auto cell : fused)
			to_remove.insert(cell);
		for (auto cell : to_remove)
			module->remove(cell);
	}

	void process_maccs()
	{
		pool<Cell *> to_remove;
		for (auto cell : macc) {
			if (GetSize(cell->getPort(ID::Y)) < opt.min_width)
				continue;

			std::vector<Operand> operands;
			std::vector<int> neg_offsets;
			if (!extract_macc_operands(cell, operands, neg_offsets))
				continue;
			if (operands.size() < 1)
				continue;
			int mul_terms = 0;
			for (auto &op : operands)
				if (GetSize(op.factor_b) > 0)
					mul_terms++;
			bool has_mul = (mul_terms > 0);
			if (mul_terms == 1 && operands.size() == 1)
				continue;
			if (!has_mul && operands.size() < 3)
				continue;
			emit_tree(cell, operands, cell->getPort(ID::Y), neg_offsets);
			to_remove.insert(cell);
		}
		for (auto cell : to_remove)
			module->remove(cell);
}

	void run()
	{
		if (addsub.empty() && alu.empty() && macc.empty())
			return;

		process_chains();
		process_maccs();
	}
};

struct ArithTreePass : public Pass {
	ArithTreePass() : Pass("arith_tree", "convert add/sub/macc/alu chains to carry-save adder trees") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    arith_tree [options] [selection]\n");
		log("\n");
		log("This pass replaces chains of $add/$sub cells, $alu cells (with constant\n");
		log("BI/CI), and $macc/$macc_v2 cells with carry-save adder trees \n");
		log("using $fa cells and a single final adder.\n");
		log("\n");
		log("    -strategy <fa|42>\n");
		log("        Compressor strategy. 'fa' uses only 3:2 full-adder groupings\n");
		log("        '42' (the default) prefers 4:2 compressor groupings, with\n");
		log("        fallback to 3:2 compressors for residuals\n");
		log("\n");
		log("    -final <auto|ripple|prefix|prefix-cmos>\n");
		log("        Selects the architecture used for the final two-vector add.\n");
		log("        'prefix' builds a Kogge-Stone adder of AND/OR/XOR gates;\n");
		log("        'prefix-cmos' builds the same prefix graph from inverting gates\n");
		log("        ($_NAND_/$_NOR_ and $_AOI3_/$_OAI3_ of alternating polarity), one\n");
		log("        gate per prefix level, for flows whose mapper would otherwise\n");
		log("        trade those levels away for area. An adder that a late product\n");
		log("        reaches past the tree (its upper bits arriving untouched, about\n");
		log("        as late as the tree's own outputs) keeps the AND/OR network.\n");
		log("\n");
		log("    -no-fma\n");
		log("        Disable fused multiply-add expansion in $macc cells\n");
		log("\n");
		log("    -fma-chains\n");
		log("        Also expand an unsigned $mul whose only reader is an add chain into\n");
		log("        partial products in that chain's tree, as FMA fusion does for $macc.\n");
		log("        The product then crosses one tree and one final adder instead of\n");
		log("        its own and the chain's.\n");
		log("\n");
		log("    -schedule\n");
		log("        Enter each operand at the level its own logic arrives, estimated\n");
		log("        from the depth of the network driving it, instead of feeding them\n");
		log("        all in at level 0. A late operand is then held back and crosses\n");
		log("        one compressor level instead of all of them; a product feeding a\n");
		log("        sum of products is the usual case. Off by default because it\n");
		log("        reorders operands on designs where the arrivals are already even.\n");
		log("\n");
		log("    -bit-offsets\n");
		log("        Place each link and leaf operand at the column it enters the sum\n");
		log("        at, instead of requiring all of them to start at the result LSB.\n");
		log("        Sums of terms weighted by different powers of two -- hand-split\n");
		log("        partial products, or any add tree a significant-width narrowing\n");
		log("        has rewritten into windowed slices -- then reduce as one tree\n");
		log("        with one final adder, where otherwise every weighted term ends\n");
		log("        a chain and keeps its own carry-propagate adder. Off by default\n");
		log("        because it admits chains across links the plain reading refuses.\n");
		log("\n");
		log("    -sext-links\n");
		log("        With -bit-offsets, also chain an unsigned difference that its\n");
		log("        consumer sign-extends by copying its MSB, which is how wreduce\n");
		log("        leaves a - b narrowed under a wider sum. Such a link is exact read\n");
		log("        as signed when its result is wider than both operands, so a - b + c\n");
		log("        reduces as one tree instead of two carry-propagate adders.\n");
		log("\n");
		log("    -cell-fa\n");
		log("        Schedule the tree at the depths of a cell library's full adder,\n");
		log("        whose carry is one gate from any input and whose sum is two gates\n");
		log("        from A or B and one from C, instead of the gate network $fa lowers\n");
		log("        to, whose carry is the later output. Early carries then compress\n");
		log("        again while their sums are still in flight, and late sums take C.\n");
		log("\n");
		log("    -min-width <n>\n");
		log("        Skip chains and $macc cells whose result is narrower than <n>\n");
		log("        bits (default 0, i.e. no limit). A compressor level costs about\n");
		log("        the same depth at any width, so compression only pays when it\n");
		log("        removes a wide carry-propagate adder; below that the plain chain\n");
		log("        (or 'opt_balance_tree') wins. Prefer this over restricting the\n");
		log("        selection: this pass indexes every cell in a selected module, so\n");
		log("        a cell-level selection only gates which modules run, and one wide\n");
		log("        adder anywhere would otherwise pull in all the narrow chains too.\n");
		log("\n");
		log("The default behaviour delivers 4:2 compression, FMA fusion, and a\n");
		log("final standard adder\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing ARITH_TREE pass.\n");

		ArithTreeOptions opt;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			const std::string &arg = args[argidx];
			if (arg == "-strategy" && argidx + 1 < args.size()) {
				const std::string &v = args[++argidx];
				if (v == "fa") { opt.strategy = CompressorTree::Strategy::FA_ONLY; }
				else if (v == "42") { opt.strategy = CompressorTree::Strategy::PREFER_42; }
				else { log_cmd_error("arith_tree: unknown -strategy '%s'\n", v.c_str()); }
				continue;
			}
			if (arg == "-final" && argidx + 1 < args.size()) {
				const std::string &v = args[++argidx];
				if (v == "auto") { opt.final_mode = CompressorTree::FinalMode::AUTO; }
				else if (v == "ripple") { opt.final_mode = CompressorTree::FinalMode::RIPPLE; }
				else if (v == "prefix") { opt.final_mode = CompressorTree::FinalMode::PREFIX; }
				else if (v == "prefix-cmos") { opt.final_mode = CompressorTree::FinalMode::PREFIX_CMOS; } // SILIMATE
				else { log_cmd_error("arith_tree: unknown -final '%s'\n", v.c_str()); }
				continue;
			}
			if (arg == "-no-fma") {
				opt.fma_fusion = false;
				continue;
			}
			if (arg == "-fma-chains") {
				opt.fma_chains = true;
				continue;
			}
			if (arg == "-schedule") {
				opt.schedule_arrival = true;
				continue;
			}
			if (arg == "-bit-offsets") {
				opt.bit_offsets = true;
				continue;
			}
			if (arg == "-sext-links") {
				opt.sext_links = true;
				continue;
			}
			if (arg == "-cell-fa") {
				opt.cell_fa = true;
				continue;
			}
			if (arg == "-min-width" && argidx + 1 < args.size()) {
				opt.min_width = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int prefix_cmos = 0, prefix_kept = 0;
		for (auto mod : design->selected_modules()) {
			// Rejoining moves the parent's other operand up a column, which only -bit-offsets can chain
			if (opt.bit_offsets)
				rejoin_stripped_lsbs(mod);
			ArithTreeWorker worker(opt, mod);
			worker.run();
			prefix_cmos += worker.prefix_cmos;
			prefix_kept += worker.prefix_kept;
		}
		// SILIMATE
		if (opt.final_mode == CompressorTree::FinalMode::PREFIX_CMOS)
			log("Built %d final adder(s) from inverting gates; kept %d as AND/OR, reached late by a product.\n",
			    prefix_cmos, prefix_kept);
	}
} ArithTreePass;

PRIVATE_NAMESPACE_END
