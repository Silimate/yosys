#include "compressor_tree.h"

YOSYS_NAMESPACE_BEGIN

namespace CompressorTree
{

// a + b + c as {sum, cout}: $fa over live columns, wires over zero padding and repeated columns, gates otherwise
static std::pair<SigSpec, SigSpec> emit_fa(Module *module, SigSpec a, SigSpec b, SigSpec c, IdString cell_name, const std::string &suffix)
{
	auto kind = [&](int i) {
		if (i > 0 && a[i] == a[i - 1] && b[i] == b[i - 1] && c[i] == c[i - 1])
			return 3;
		int live = (a[i].wire != nullptr) + (b[i].wire != nullptr) + (c[i].wire != nullptr);
		bool zeros = (a[i].wire || a[i] == State::S0) && (b[i].wire || b[i] == State::S0) && (c[i].wire || c[i] == State::S0);
		return live == 3 ? 2 : zeros && live <= 1 ? 0 : 1;
	};
	SigSpec sum, cout;
	for (int lo = 0, hi; lo < GetSize(a); lo = hi) {
		for (hi = lo + 1; hi < GetSize(a) && kind(hi) == kind(lo); hi++);
		int n = hi - lo;
		// Sign extension repeats the column below, and so do its outputs
		if (kind(lo) == 3) {
			sum.append(SigSpec(sum[GetSize(sum) - 1], n));
			cout.append(SigSpec(cout[GetSize(cout) - 1], n));
			continue;
		}
		if (kind(lo) == 0) {
			for (int i = lo; i < hi; i++)
				sum.append(a[i].wire ? a[i] : b[i].wire ? b[i] : c[i]);
			cout.append(SigSpec(State::S0, n));
			continue;
		}
		SigSpec sa = a.extract(lo, n), sb = b.extract(lo, n), sc = c.extract(lo, n);
		SigSpec s = module->addWire(NEW_ID3_SUFFIX(suffix + "_sum"), n); // SILIMATE: Improve the naming
		SigSpec co = module->addWire(NEW_ID3_SUFFIX(suffix + "_cout"), n); // SILIMATE: Improve the naming
		if (kind(lo) == 2) {
			module->addFa(NEW_ID3_SUFFIX(suffix), sa, sb, sc, co, s); // SILIMATE: Improve the naming
		} else {
			SigSpec t1 = module->Xor(NEW_ID3_SUFFIX(suffix + "_xor"), sa, sb);
			module->addXor(NEW_ID3_SUFFIX(suffix + "_xor"), t1, sc, s);
			module->addOr(NEW_ID3_SUFFIX(suffix + "_or"), module->And(NEW_ID3_SUFFIX(suffix + "_and"), sa, sb),
					module->And(NEW_ID3_SUFFIX(suffix + "_and"), sc, t1), co);
		}
		sum.append(s);
		cout.append(co);
	}
	return {sum, cout};
}

std::pair<SigSpec, SigSpec> emit_compressor_32(Module *module, SigSpec a, SigSpec b, SigSpec c, int width, IdString cell_name)
{
	auto [sum, cout] = emit_fa(module, a, b, c, cell_name, "fa");

	SigSpec carry;
	carry.append(State::S0);
	carry.append(cout.extract(0, width - 1));
	return {sum, carry};
}

std::pair<SigSpec, SigSpec> emit_compressor_42(Module *module, SigSpec a, SigSpec b, SigSpec c, SigSpec d, int width, IdString cell_name)
{
	// First FA: a + b + c -> s0
	auto [s0, cout_h_full] = emit_fa(module, a, b, c, cell_name, "c42_lo");

	// cin[0] = 0, cin[i] = cout_h_full[i-1]
	SigSpec cin;
	cin.append(State::S0);
	if (width > 1)
		cin.append(cout_h_full.extract(0, width - 1));

	// Second FA: s0 + d + cin -> sum
	auto [sum, carry_full] = emit_fa(module, s0, d, cin, cell_name, "c42_hi");

	SigSpec carry;
	carry.append(State::S0);
	if (width > 1)
		carry.append(carry_full.extract(0, width - 1));

	return {sum, carry};
}

std::vector<DepthSig> generate_partial_products(Module *module, SigSpec a, SigSpec b, bool a_signed, bool b_signed, int width, IdString cell_name) {
	int width_a = GetSize(a);
	int width_b = GetSize(b);
	std::vector<DepthSig> products;
	products.reserve(width_a + 3);

	for (int i = 0; i < width_a; i++) {
		SigBit ai = a[i];

		// b_shifted = (0_i ## b)
		SigSpec b_shifted = SigSpec(State::S0, i);
		b_shifted.append(b);
		b_shifted.extend_u0(width, false);

		// row = b_shifted & replicate(a[i], width)
		SigSpec ai_rep = SigSpec(ai, width);
		SigSpec row = module->addWire(NEW_ID3_SUFFIX("pp"), width); // SILIMATE: Improve the naming
		module->addAnd(NEW_ID3_SUFFIX("pp_and"), b_shifted, ai_rep, row); // SILIMATE: Improve the naming

		// Apply Modified Baugh-Wooley inversions for this row
		bool row_is_bottom = (i == width_a - 1);
		bool any_inversion = (row_is_bottom && b_signed) || a_signed;

		if (any_inversion) {
			std::vector<RTLIL::State> mask(width, RTLIL::State::S0);

			for (int j = 0; j < width_b; j++) {
				int col = i + j;
				if (col < 0 || col >= width)
					continue;
				bool col_is_right = (j == width_b - 1);
				// Flip masks
				bool invert = (row_is_bottom && b_signed) ^ (col_is_right && a_signed);
				if (invert)
					mask[col] = RTLIL::State::S1;
			}

			// Skip the xor entirely if the mask is all zeroes
			bool nonzero = false;
			for (auto s : mask)
				if (s == RTLIL::State::S1) {
					nonzero = true;
					break;
				}
			if (nonzero) {
				SigSpec inverted = module->addWire(NEW_ID3_SUFFIX("pp_inv"), width); // SILIMATE: Improve the naming
				module->addXor(NEW_ID3_SUFFIX("pp_xor"), row, SigSpec(RTLIL::Const(mask)), inverted); // SILIMATE: Improve the naming
				row = inverted;
			}
		}

		products.push_back({row, 0});
	}

	// Correction constants
	auto push_one_at = [&](int col) {
		if (col < 0 || col >= width)
			return;
		std::vector<RTLIL::State> v(width, RTLIL::State::S0);
		v[col] = RTLIL::State::S1;
		products.push_back({SigSpec(RTLIL::Const(v)), 0});
	};

	if (b_signed)
		push_one_at(width_a - 1);
	if (a_signed)
		push_one_at(width_b - 1);
	if (a_signed || b_signed)
		push_one_at(width_a + width_b - 1);

	return products;
}

std::pair<SigSpec, SigSpec> reduce_scheduled(Module *module, std::vector<DepthSig> operands, int width, Strategy strategy, IdString cell_name, int *out_compressor_count, int *out_final_depth) {
	int levels = 0;
	int fa_count = 0;
	int c42_count = 0;
	int final_depth = 0;

	for (auto &op : operands)
		op.sig.extend_u0(width);

	// Earliest level with three operands ready, i.e. the third-shallowest of them.
	// Depths are gate delays, so stepping a level at a time would spin over levels
	// with nothing to compress.
	auto third_shallowest = [](const std::vector<DepthSig> &ops) {
		// Runs once more after the last round leaves two operands, which cannot be
		// compressed and so have no next level
		if (GetSize(ops) < 3)
			return 0;
		std::vector<int> d;
		d.reserve(ops.size());
		for (auto &op : ops)
			d.push_back(op.depth);
		std::nth_element(d.begin(), d.begin() + 2, d.end());
		return d[2];
	};

	// Only compress operands ready at current level
	for (int level = 0; operands.size() > 2; level = std::max(level + 1, third_shallowest(operands))) {
		// Partition operands into ready and waiting
		std::vector<DepthSig> ready;
		std::vector<DepthSig> waiting;
		ready.reserve(operands.size());
		for (auto &op : operands) {
			if (op.depth <= level)
				ready.push_back(op);
			else
				waiting.push_back(op);
		}

		if (ready.size() < 3) {
			continue;
		}

		// Compress the earliest operands first, so an operand that only just became
		// ready is not buried under one that has been waiting, and so each group's
		// latest lands on its shallowest input: C on a 3:2, and the second adder's
		// B on a 4:2, whose other three slots sit behind both adders
		std::stable_sort(ready.begin(), ready.end(), [](const DepthSig &a, const DepthSig &b) { return a.depth < b.depth; });

		// Apply compressors to ready operands
		std::vector<DepthSig> compressed;
		compressed.reserve(ready.size());
		size_t i = 0;

		// PREFER_42 attempts 4:2 grouping greedily (falls back to 3:2 for the residual)
		// FA_ONLY skips
		// DADDA = PREFER_42 (TODO: inspect column heights?)
		bool try_42 = (strategy == Strategy::PREFER_42 || strategy == Strategy::DADDA);

		while (i < ready.size()) {
			size_t remaining = ready.size() - i;

			if (try_42 && remaining >= 4) {
				DepthSig a = ready[i + 0];
				DepthSig b = ready[i + 1];
				DepthSig c = ready[i + 2];
				DepthSig d = ready[i + 3];

				auto [sum, carry] = emit_compressor_42(module, a.sig, b.sig, c.sig, d.sig, width, cell_name);
				// Two chained full adders: the first's carry is the second's C
				int inner = fa_out_depth(a.depth, b.depth, c.depth);
				int out = fa_out_depth(inner, d.depth, inner);

				compressed.push_back({sum, out});
				compressed.push_back({carry, out});

				fa_count += 2;
				c42_count += 1;
				i += 4;
			} else if (remaining >= 3) {
				DepthSig a = ready[i + 0];
				DepthSig b = ready[i + 1];
				DepthSig c = ready[i + 2];

				auto [sum, carry] = emit_compressor_32(module, a.sig, b.sig, c.sig, width, cell_name);
				int out = fa_out_depth(a.depth, b.depth, c.depth);

				compressed.push_back({sum, out});
				compressed.push_back({carry, out});

				fa_count += 1;
				i += 3;
			} else {
				// Uncompressed operands pass through to next level
				for (; i < ready.size(); i++)
					compressed.push_back(ready[i]);
				break;
			}
		}

		// Merge compressed with waiting operands
		for (auto &op : waiting)
			compressed.push_back(op);

		operands = std::move(compressed);
		levels++;
	}

	if(out_compressor_count)
		*out_compressor_count = fa_count;
	if (operands.size() == 0) {
		if (out_final_depth)
			*out_final_depth = 0;
		return {SigSpec(State::S0, width), SigSpec(State::S0, width)};
	}
	if (operands.size() == 1) {
		if (out_final_depth)
			*out_final_depth = operands[0].depth;
		return {operands[0].sig, SigSpec(State::S0, width)};
	}

	final_depth = std::max(operands[0].depth, operands[1].depth);
	if (out_final_depth)
		*out_final_depth = final_depth;
	log_assert(operands.size() == 2);
	log("    CompressorTree::reduce_scheduled: %d levels, %d 3:2 compressors (%d as 4:2), final depth %d\n", levels, fa_count, c42_count, final_depth);
	return {operands[0].sig, operands[1].sig};
}

void emit_kogge_stone(Module *module, SigSpec a, SigSpec b, SigSpec y, IdString cell_name)
{
	int width = GetSize(y);
	log_assert(GetSize(a) == width);
	log_assert(GetSize(b) == width);

	if (width == 0)
		return;

	if (width == 1) {
		module->addXorGate(NEW_ID3_SUFFIX("ks_sum"), a[0], b[0], y[0]); // SILIMATE: Improve the naming
		return;
	}

	// Bit level gen and prop
	std::vector<SigBit> g_pre(width), p_pre(width);
	for (int i = 0; i < width; i++) {
		SigBit gi = module->addWire(NEW_ID3_SUFFIX("ks_g")); // SILIMATE: Improve the naming
		SigBit pi = module->addWire(NEW_ID3_SUFFIX("ks_p")); // SILIMATE: Improve the naming
		module->addAndGate(NEW_ID3_SUFFIX("ks_g_and"), a[i], b[i], gi); // SILIMATE: Improve the naming
		module->addXorGate(NEW_ID3_SUFFIX("ks_p_xor"), a[i], b[i], pi); // SILIMATE: Improve the naming
		g_pre[i] = gi;
		p_pre[i] = pi;
	}

	// Propagate (g, p) through ceil(log2 W) levels
	std::vector<SigBit> g = g_pre;
	std::vector<SigBit> p = p_pre;
	int num_levels = 0;

	while ((1 << num_levels) < width)
		num_levels++;

	for (int k = 1; k <= num_levels; k++) {
		int s = 1 << (k - 1);
		std::vector<SigBit> g_next(width), p_next(width);
		for (int i = 0; i < width; i++) {
			if (i < s) {
				// Nothing to do
				g_next[i] = g[i];
				p_next[i] = p[i];
			} else {
				// g_i^k = g_i | (p_i & g_(i-s))
				SigBit and_pg = module->addWire(NEW_ID3_SUFFIX("ks_pg")); // SILIMATE: Improve the naming
				module->addAndGate(NEW_ID3_SUFFIX("ks_pg_and"), p[i], g[i - s], and_pg); // SILIMATE: Improve the naming
				SigBit gnew = module->addWire(NEW_ID3_SUFFIX("ks_gnext")); // SILIMATE: Improve the naming
				module->addOrGate(NEW_ID3_SUFFIX("ks_g_or"), g[i], and_pg, gnew); // SILIMATE: Improve the naming
				g_next[i] = gnew;

				// p_i^k = p_i & p_(i-s)
				if (k < num_levels) {
					SigBit pnew = module->addWire(NEW_ID3_SUFFIX("ks_pnext")); // SILIMATE: Improve the naming
					module->addAndGate(NEW_ID3_SUFFIX("ks_p_and"), p[i], p[i - s], pnew); // SILIMATE: Improve the naming
					p_next[i] = pnew;
				} else {
					// Skip last level
					p_next[i] = State::Sx;
				}
			}
		}

		g = std::move(g_next);
		p = std::move(p_next);
	}

	// Sum layer, g[i] is COUT of bit i
	// With CIN 0:
	//   sum[0] = p_pre[0]
	//   sum[i] = p_pre[i] ^ g[i-1] ...
	module->connect(y[0], p_pre[0]);
	for (int i = 1; i < width; i++)
		module->addXorGate(NEW_ID3_SUFFIX("ks_sum"), p_pre[i], g[i - 1], y[i]); // SILIMATE: Improve the naming
}

Cell *emit_final_adder(Module *module, SigSpec a, SigSpec b, SigSpec y, FinalAdder choice, IdString cell_name) {
	switch (choice) {
		case FinalAdder::DEFAULT:
		case FinalAdder::RIPPLE: {
			return module->addAdd(NEW_ID3_SUFFIX("cpa"), a, b, y, false); // SILIMATE: Improve the naming
		}
		case FinalAdder::PARALLEL_PREFIX: {
			emit_kogge_stone(module, a, b, y, cell_name);
			return nullptr;
		}
	}
	log_assert(false && "CompressorTree::emit_final_adder: invalid choice");
	return nullptr;
}

FinalAdder pick_final_adder(int width, int final_depth, FinalMode mode) {
	switch (mode) {
		case FinalMode::RIPPLE:  return FinalAdder::RIPPLE;
		case FinalMode::PREFIX:  return FinalAdder::PARALLEL_PREFIX;
		case FinalMode::AUTO:
		default: {
			bool wide = width >= RIPPLE_PREFIX_WIDTH_THRESHOLD;
			bool deep = final_depth >= RIPPLE_PREFIX_DEPTH_THRESHOLD;
			return (wide && deep) ? FinalAdder::PARALLEL_PREFIX : FinalAdder::DEFAULT;
		}
	}
}

} // namespace CompressorTree

YOSYS_NAMESPACE_END
