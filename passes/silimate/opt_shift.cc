/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *                      Akash Levy <akash@silimate.com>
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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "passes/opt/rewrite_utils.h"

bool did_something;

// Driver index for the module being processed, rebuilt per module by the sink
// pattern so it can walk back from a shift amount to the cell producing it.
SigMap sink_sigmap;
dict<SigBit, Cell *> sink_drivers;

void sink_index_module(Module *module)
{
  sink_sigmap.set(module);
  sink_drivers.clear();
  for (auto cell : module->cells())
    for (auto &conn : cell->connections())
      if (cell->output(conn.first))
        for (auto bit : sink_sigmap(conn.second))
          sink_drivers[bit] = cell;
}

// Cheap pre-filter for the patterns that need a barrel: a constant amount is
// already folded by -combine, so without a variable shifter of one of `types`
// there is nothing to match. -sink and -fuse rewrite a left shift, -push a
// right one, so each passes the types it can actually use.
bool has_variable_shift(Module *module, const pool<IdString> &types)
{
  for (auto cell : module->selected_cells())
    if (types.count(cell->type) && !cell->getPort(ID::B).is_fully_const())
      return true;
  return false;
}

int min_shift_amount(SigSpec amt, int depth = 3);

// Largest value an amount can take, discounting constant-zero high bits. -1 when
// the range is too wide to enumerate, which every caller treats as a refusal.
int max_shift_amount(SigSpec amt)
{
  int w = GetSize(amt);
  while (w > 0 && amt[w - 1] == State::S0)
    w--;
  return w > 20 ? -1 : (1 << w) - 1;
}

// Lower bound on `chunk`, which must be the complete output of `drv`. Only
// unsigned "var + const" is understood; anything else contributes nothing.
int min_driven_value(Cell *drv, const SigSpec &chunk, int depth)
{
  if (drv->type != ID($add))
    return 0;
  if (drv->getParam(ID::A_SIGNED).as_bool() || drv->getParam(ID::B_SIGNED).as_bool())
    return 0;
  if (sink_sigmap(drv->getPort(ID::Y)) != chunk)
    return 0;

  SigSpec a = sink_sigmap(drv->getPort(ID::A)), b = sink_sigmap(drv->getPort(ID::B));
  bool a_const = a.is_fully_const();
  SigSpec cst = a_const ? a : b, var = a_const ? b : a;
  if (!cst.is_fully_const() || !cst.is_fully_def() || GetSize(var) > 24)
    return 0;

  // as_int truncates, which stays correct modulo the chunk width, but a set
  // bit 31 would come back negative and poison the shift in the caller
  int c = cst.as_int();
  if (c < 0)
    return 0;

  // A sum that can wrap would break the bound, so require it to always fit
  if (((1 << GetSize(var)) - 1) + c >= (1 << GetSize(chunk)))
    return 0;
  return c + min_shift_amount(var, depth - 1);
}

// Sound lower bound on the value a shift amount can take. A sum is at least
// the sum of its parts' minima, so each maximal same-driver run of bits is
// bounded on its own and the pieces are weighted back in by bit position.
// Under-estimates rather than over-estimates, so callers stay safe.
int min_shift_amount(SigSpec amt, int depth)
{
  amt = sink_sigmap(amt);
  if (GetSize(amt) > 24) // keep the shifts below inside int range
    return 0;

  int bound = 0;
  for (int i = 0; i < GetSize(amt); ) {
    // Constant bits are set in every reachable value
    if (!amt[i].is_wire()) {
      if (amt[i] == State::S1)
        bound += 1 << i;
      i++;
      continue;
    }
    if (depth <= 0 || !sink_drivers.count(amt[i])) {
      i++;
      continue;
    }

    // Extend over the run of bits fed by the same cell
    Cell *drv = sink_drivers.at(amt[i]);
    int j = i;
    while (j < GetSize(amt) && amt[j].is_wire() && sink_drivers.count(amt[j]) &&
           sink_drivers.at(amt[j]) == drv)
      j++;

    bound += min_driven_value(drv, amt.extract(i, j - i), depth) << i;
    i = j;
  }
  return bound;
}

// Fuse a modular gather with the variable shift feeding it. opt_vps lowers a
// bit-select farm to one $shr over its table rotated by a constant and padded
// with x, so when that table is a shifter output the two barrels sit back to
// back and -combine cannot merge them: the rotation leaves the outer A port a
// permutation of the inner Y rather than the same SigSpec.
//
//   out[t] = pad_M(x << b)[(t + a + r) % M]
//     ===>  out[t] = pad_M(x & (~0 >> b))[(t + a + r - b) % M]
//
// Masking x drops the high bits the rotate would otherwise wrap in underneath
// the left shift's zero fill, which is the only place the two disagree. What is
// left is a single barrel over a repeated source, so one shifter leaves every
// path through the gather in exchange for a mask that depends on b alone.
// The shifter itself stays if other cells read it; opt_clean sweeps it if not.
struct GatherFuser
{
  Module *module;
  SigMap sigmap;
  dict<SigBit, Cell *> drivers;
  int max_src_bits;
  int fused = 0;

  GatherFuser(Module *module, int max_src_bits)
    : module(module), sigmap(module), max_src_bits(max_src_bits)
  {
    for (auto cell : module->cells())
      for (auto &conn : cell->connections())
        if (cell->output(conn.first))
          for (auto bit : sigmap(conn.second))
            drivers[bit] = cell;
  }

  // Read `outer`'s A port as one $shl output rotated by a constant: every
  // defined bit must be inner_y[(j + rot) % mod] for a single rot, and every x
  // must rotate above inner_y, where it was padding rather than a table entry.
  Cell *match_rotated_source(Cell *outer, int &rot, int &mod)
  {
    SigSpec s = sigmap(outer->getPort(ID::A));

    Cell *inner = nullptr;
    for (auto bit : s) {
      if (!bit.is_wire())
        continue;
      auto it = drivers.find(bit);
      if (it == drivers.end() || (inner && it->second != inner))
        return nullptr;
      inner = it->second;
    }
    if (!inner || inner->type != ID($shl) || inner->getPort(ID::B).is_fully_const())
      return nullptr;
    if (inner->getParam(ID::A_SIGNED).as_bool() || inner->getParam(ID::B_SIGNED).as_bool())
      return nullptr;

    SigSpec iy = sigmap(inner->getPort(ID::Y));
    int wy = GetSize(iy);
    if (wy < 2 || wy > (1 << 20)) // keep the table and 1 << clog2 in range
      return nullptr;
    mod = 1 << clog2_int(wy);
    if (GetSize(sigmap(inner->getPort(ID::A))) > mod) // mask is only mod bits wide
      return nullptr;

    dict<SigBit, int> index;
    for (int i = 0; i < wy; i++)
      index.emplace(iy[i], i);

    rot = -1;
    for (int j = 0; j < GetSize(s); j++) {
      if (s[j] == State::Sx)
        continue;
      auto it = index.find(s[j]);
      if (it == index.end()) // a defined bit from anywhere but inner_y
        return nullptr;
      int r = ((it->second - j) % mod + mod) % mod;
      if (rot < 0)
        rot = r;
      else if (rot != r)
        return nullptr;
    }
    if (rot < 0)
      return nullptr;

    // An x rotating onto a real inner_y bit was a table entry, not padding
    for (int j = 0; j < GetSize(s); j++)
      if (s[j] == State::Sx && (j + rot) % mod < wy)
        return nullptr;

    return inner;
  }

  void fuse(Cell *outer, Cell *inner, int rot, int mod)
  {
    SigSpec x = sigmap(inner->getPort(ID::A));
    SigSpec b = sigmap(inner->getPort(ID::B));
    SigSpec a = sigmap(outer->getPort(ID::B));
    int wx = GetSize(x), wo = outer->getParam(ID::Y_WIDTH).as_int();
    int amt_bits = clog2_int(mod);
    std::string src = cell_src(outer);

    // keep[u] = u < mod - b, the positions the left shift did not zero out.
    // Shifting a constant lowers to a decoder, and it depends only on b, so
    // the mask costs no depth on the data path.
    Wire *keep = module->addWire(NEW_ID_SUFFIX("shift_fuse_keep"), mod);
    module->addShr(NEW_ID_SUFFIX("shift_fuse_keep_shr"), Const(State::S1, mod), b,
                   SigSpec(keep), false, src);
    Wire *masked = module->addWire(NEW_ID_SUFFIX("shift_fuse_a"), wx);
    module->addAnd(NEW_ID_SUFFIX("shift_fuse_and"), x, SigSpec(keep).extract(0, wx),
                   SigSpec(masked), false, src);

    // amt = (a + rot - b) mod `mod`, wrapped by the amt_bits-wide arithmetic
    Wire *sum = module->addWire(NEW_ID_SUFFIX("shift_fuse_rot"), amt_bits);
    module->addAdd(NEW_ID_SUFFIX("shift_fuse_add"), a, const_u64(rot, amt_bits),
                   SigSpec(sum), false, src);
    Wire *amt = module->addWire(NEW_ID_SUFFIX("shift_fuse_amt"), amt_bits);
    module->addSub(NEW_ID_SUFFIX("shift_fuse_sub"), SigSpec(sum), b, SigSpec(amt),
                   false, src);

    // Repeating the masked source turns the modular access into a plain shift
    SigSpec period = SigSpec(masked);
    period.append(SigSpec(State::S0, mod - wx));
    SigSpec source;
    while (GetSize(source) < wo + mod - 1)
      source.append(period);
    source = source.extract(0, wo + mod - 1);

    log("  shift fuse: %s absorbs %s (M=%d, rot=%d, src=%d bits)\n",
        log_id(outer->name), log_id(inner->name), mod, rot, GetSize(source));

    // The shifter stays for its other readers; opt_clean sweeps it when the
    // gather was the only one
    outer->setPort(ID::A, source);
    outer->setPort(ID::B, SigSpec(amt));
    outer->fixup_parameters();
    fused++;
  }

  // Fuse at most one gather, so the caller reindexes before looking for more
  bool run()
  {
    for (auto cell : module->selected_cells()) {
      if (cell->type != ID($shr) || cell->getPort(ID::B).is_fully_const())
        continue;
      if (cell->getParam(ID::A_SIGNED).as_bool() || cell->getParam(ID::B_SIGNED).as_bool())
        continue;

      int rot, mod;
      Cell *inner = match_rotated_source(cell, rot, mod);
      if (!inner)
        continue;

      // A gather that can shift past its source zero-fills there, where the
      // rotate would instead wrap the table back around
      int wo = cell->getParam(ID::Y_WIDTH).as_int();
      int amax = max_shift_amount(sigmap(cell->getPort(ID::B)));
      if (amax < 0 || wo - 1 + amax >= GetSize(cell->getPort(ID::A)))
        continue;
      if (wo + mod - 1 > max_src_bits)
        continue;

      fuse(cell, inner, rot, mod);
      return true;
    }
    return false;
  }
};

// ---------------------------------------------------------------------------
// -push: push a variable right shift through a per-bit merge, so the barrel
// feeding one side of the merge composes with it
//
//   ((S ? b : a) >> s)[j]  ===>  (S >> s)[j] ? (b >> s)[j] : (a >> s)[j]
//
// which holds bit by bit because all four shifts drop the same positions and
// zero-fill the rest. On its own that trades one barrel for three, so it only
// fires when a side is itself a variable right shift, which then composes into
// a single barrel over a padded source:
//
//   a[i] = (x >> g)[i - k]  ===>  a >> s  =  {x, k'0} >> (g + s)
//
// leaving one barrel where the chain had two, the width of the merge apart. An
// address mapper puts exactly this shape together: a bit-select farm (which
// opt_vps lowers to a barrel), a merge, and a shift, which -combine cannot pair
// up because the merge sits between them. The other side and the select word
// pick up a barrel each, but in a mapper both are fed by configuration rather
// than by the data path.
//
// muxpush does the word-level version of this move, but not this one: a merge
// whose select differs per bit is not one $mux to hoist, and the rewrite needs
// the select word shifted alongside the data, which a hoisted mux cannot say.
//
// Two places where the composed source is not `a` shifted, and the rewrite has
// to say so:
//
//   - It is wider, so where `a >> s` would zero-fill -- past the top of the
//     merge -- it keeps delivering bits of x instead. The select is oriented so
//     that a 1 picks the composed side, which puts the other side's own zero
//     fill there.
//   - Its low k positions are pad, not the bits `a` held below x, so the output
//     bits that read them keep the merge instead.
// ---------------------------------------------------------------------------
struct MergePusher
{
  Module *module;
  SigMap sigmap;
  dict<SigBit, Cell *> drivers;
  dict<SigBit, int> readers; // reader count, to tell a private merge from a shared one
  int max_offset;
  int pushed = 0;

  // One accepted rewrite: `outer` shifts `merged`, one of whose sides is
  // `inner`'s output raised by k. `other` is the side that keeps its own
  // shifter, and `sel` selects `inner`'s side when it is 1 -- inverted from the
  // mux's own select when the match landed on the A side, which a mux reads on 0.
  struct Candidate {
    Cell *outer = nullptr, *inner = nullptr;
    SigSpec merged, other, sel;
    int k = 0, amt_bits = 0;
    int levels = 0;  // mux levels the removed barrel costs, which is what to maximize
    bool invert = false;
  };

  MergePusher(Module *module, int max_offset)
    : module(module), sigmap(module), max_offset(max_offset)
  {
    for (auto cell : module->cells())
      for (auto &conn : cell->connections()) {
        if (cell->output(conn.first)) {
          for (auto bit : sigmap(conn.second))
            drivers[bit] = cell;
          continue;
        }
        for (auto bit : sigmap(conn.second))
          readers[bit]++;
      }
    // A module connection is a reader this pass cannot rewrite either
    for (auto &conn : module->connections())
      for (auto bit : sigmap(conn.second))
        readers[bit]++;
  }

  // Read `word` as a bitwise merge: every bit driven by its own 1-bit $mux, read
  // by nothing but the shift being pushed, so that consuming the muxes does not
  // leave the merge alive beside its replacement.
  bool match_merge(const SigSpec &word, SigSpec &a, SigSpec &b, SigSpec &s)
  {
    for (auto bit : word) {
      auto it = drivers.find(bit);
      if (it == drivers.end() || it->second->type != ID($mux))
        return false;
      Cell *mux = it->second;
      if (mux->getParam(ID::WIDTH).as_int() != 1 || sigmap(mux->getPort(ID::Y)) != bit)
        return false;
      if (readers.at(bit) != 1)
        return false;
      a.append(sigmap(mux->getPort(ID::A)));
      b.append(sigmap(mux->getPort(ID::B)));
      s.append(sigmap(mux->getPort(ID::S)));
    }
    return !word.empty();
  }

  bool is_plain_shr(Cell *cell)
  {
    return cell->type == ID($shr) && !cell->getPort(ID::B).is_fully_const() &&
           !cell->getParam(ID::A_SIGNED).as_bool() && !cell->getParam(ID::B_SIGNED).as_bool();
  }

  // Read `word` as a variable right shift's output raised by a constant, so
  // word[i] == shift.Y[i - k] for every i the composed barrel has to serve
  Cell *match_raised_shift(const SigSpec &word, int &k)
  {
    int w = GetSize(word);
    auto it = drivers.find(word[w - 1]);
    if (it == drivers.end() || !is_plain_shr(it->second))
      return nullptr;
    Cell *shift = it->second;

    SigSpec y = sigmap(shift->getPort(ID::Y));
    dict<SigBit, int> index;
    for (int i = 0; i < GetSize(y); i++)
      index.emplace(y[i], i);

    auto top = index.find(word[w - 1]);
    if (top == index.end())
      return nullptr;
    k = (w - 1) - top->second;
    if (k < 0 || w - k > GetSize(y))
      return nullptr;

    // Every position from k up has to be the shift's own bit, or the composed
    // barrel would serve a value the merge never held there
    for (int i = k; i < w; i++) {
      auto at = index.find(word[i]);
      if (at == index.end() || at->second != i - k)
        return nullptr;
    }
    return shift;
  }

  // `sig` shifted right by the outer amount, into a fresh `width`-bit wire
  SigSpec shift_by_amount(Cell *outer, const SigSpec &sig, int width, const char *tag,
                          const std::string &src)
  {
    Wire *y = module->addWire(NEW_ID_SUFFIX(tag), width);
    module->addShr(NEW_ID_SUFFIX(tag), sig, sigmap(outer->getPort(ID::B)), SigSpec(y), false,
                   src);
    return SigSpec(y);
  }

  void push(const Candidate &c)
  {
    Cell *outer = c.outer;
    // Drive the bits the cell itself drives, not their sigmap representatives,
    // which an alias elsewhere in the module can move off this wire
    SigSpec out = outer->getPort(ID::Y);
    int wo = GetSize(out);
    std::string src = cell_src(outer);

    // Padding the source by k lines the barrel up with the merge's indices,
    // which keeps the composed amount a plain sum of the two amounts
    SigSpec source(State::S0, c.k);
    source.append(sigmap(c.inner->getPort(ID::A)));
    Wire *amt = module->addWire(NEW_ID_SUFFIX("shift_push_amt"), c.amt_bits);
    module->addAdd(NEW_ID_SUFFIX("shift_push_add"), sigmap(c.inner->getPort(ID::B)),
                   sigmap(outer->getPort(ID::B)), SigSpec(amt), false, src);
    Wire *taken = module->addWire(NEW_ID_SUFFIX("shift_push_a"), wo);
    module->addShr(NEW_ID_SUFFIX("shift_push_a_shr"), source, SigSpec(amt), SigSpec(taken),
                   false, src);

    // The other side shifts on its own, and so does the select, oriented to pick
    // the composed side on a 1. Past the top of the merge, where every shift
    // zero-fills, the select is then 0 and the mux reads the other side's fill
    // rather than the composed source, which has none there.
    SigSpec other = shift_by_amount(outer, c.other, wo, "shift_push_b", src);
    SigSpec picked = c.sel;
    if (c.invert) {
      Wire *inv = module->addWire(NEW_ID_SUFFIX("shift_push_sn"), GetSize(c.sel));
      module->addNot(NEW_ID_SUFFIX("shift_push_not"), c.sel, SigSpec(inv), false, src);
      picked = SigSpec(inv);
    }
    SigSpec sel = shift_by_amount(outer, picked, wo, "shift_push_s", src);

    // Output bits landing in the source's pad get the merge instead. Both words
    // are one shift of a k-bit word, so they cost no depth of their own:
    // (~0 >> s)[j] is 1 exactly when j + s < k, and (merged[k-1:0] >> s)[j] is
    // the merge bit j + s that belongs there.
    SigSpec keep, from_merge;
    if (c.k > 0) {
      keep = shift_by_amount(outer, Const(State::S1, c.k), c.k, "shift_push_keep", src);
      from_merge = shift_by_amount(outer, c.merged.extract(0, c.k), c.k, "shift_push_low", src);
    }

    for (int j = 0; j < wo; j++) {
      bool patch = j < c.k;
      SigBit y = patch ? SigBit(module->addWire(NEW_ID_SUFFIX("shift_push_y"))) : out[j];
      module->addMux(NEW_ID_SUFFIX("shift_push_mux"), other[j], SigSpec(taken, j), sel[j], y,
                     src);
      if (patch)
        module->addMux(NEW_ID_SUFFIX("shift_push_low_mux"), y, from_merge[j], keep[j], out[j],
                       src);
    }

    log("  shift push: %s through a %d-bit merge onto %s (offset %d)\n", log_id(outer->name),
        GetSize(c.merged), log_id(c.inner->name), c.k);
    module->remove(outer);
    pushed++;
  }

  bool reject(Cell *cell, const char *why)
  {
    log_debug("  %s: no push, %s\n", log_id(cell->name), why);
    return false;
  }

  bool collect(Cell *cell, Candidate &c)
  {
    if (!is_plain_shr(cell) || cell->get_bool_attribute(ID::keep))
      return false;

    // The rewrite drives Y from muxes instead, which needs Y to be a net this
    // pass may redrive: not a constant, an input port, or a kept probe
    for (auto bit : cell->getPort(ID::Y))
      if (!bit.wire || bit.wire->port_input || bit.wire->get_bool_attribute(ID::keep))
        return reject(cell, "its output is not this pass's to redrive");

    c.outer = cell;
    c.merged = sigmap(cell->getPort(ID::A));
    SigSpec a, b, s;
    if (!match_merge(c.merged, a, b, s))
      return reject(cell, "its source is not a merge of 1-bit muxes it alone reads");

    // Without a barrel to compose with, pushing would just triple this one
    c.inner = match_raised_shift(b, c.k);
    c.other = a;
    c.sel = s;
    c.invert = false;
    if (!c.inner) {
      c.inner = match_raised_shift(a, c.k);
      c.other = b;
      c.invert = true;
    }
    if (!c.inner || c.inner == cell)
      return reject(cell, "neither side of the merge is a variable right shift");

    int outer_max = max_shift_amount(sigmap(cell->getPort(ID::B)));
    int inner_max = max_shift_amount(sigmap(c.inner->getPort(ID::B)));
    if (outer_max < 0 || inner_max < 0)
      return reject(cell, "an amount range is too wide to compose");

    // Each padded position costs an output bit that keeps the merge, in place of
    // the barrel this removes, so bound the offset and require the merge to be
    // wide enough for the removed barrel to be the deeper of the two. The width
    // test also rules out a 1-bit "barrel", which is an AND, not a shifter, and
    // bounds the recursion: the merge a push leaves behind is only k bits wide.
    if (c.k > max_offset)
      return reject(cell, "the merge sits further above the inner shift than the limit");
    if (GetSize(c.merged) <= 2 * std::max(c.k, 1))
      return reject(cell, "the merge is too narrow to pay for the offset");

    // Wide enough that the composed amount cannot wrap at either extreme
    c.amt_bits = clog2_int(inner_max + outer_max + 1);

    // A barrel is one mux level per bit of amount range, so that is the depth
    // this rewrite buys, independent of how wide the shifted word is
    c.levels = clog2_int(outer_max + 1);
    return true;
  }

  // Push at most one shift, so the caller reindexes before looking for more
  bool run()
  {
    Candidate best;
    for (auto cell : module->selected_cells()) {
      Candidate c;
      if (!collect(cell, c))
        continue;
      // A push consumes the barrel it lands on, so candidates can exclude each
      // other; taking the deepest barrel first is what makes the choice pay
      if (!best.outer || c.levels > best.levels)
        best = c;
    }
    if (!best.outer)
      return false;
    push(best);
    return true;
  }
};

// ---------------------------------------------------------------------------
// -descale: collapse a scale-down round trip around a variable right shift
//
//   ((x + 1) >> s) - 1   ===>   c ? (x >> s) : (x >> s) - 1,  c = &x[s-1:0]
//
// Writing x = t*2^s + r, the shift throws r away, so the only thing the
// increment can still contribute past it is its carry out of that window, which
// is exactly c (vacuously true for s == 0). Absorbing that carry downstream
// leaves one carry chain instead of two bracketing the shifter, and the window
// test is a log-depth AND scan that runs beside it rather than ahead of it.
// ---------------------------------------------------------------------------

// Unsigned constant 1 of any width
bool descale_is_one(const SigSpec &sig)
{
  return GetSize(sig) > 0 && sig.is_fully_const() && sig.as_const() == Const(1, GetSize(sig));
}

// `out - 1`, reading `out` from bit 0 up. A narrower read is fine: the carry
// identity holds mod 2^k for any k, so a decrement that wreduce has already
// narrowed to what its own result needs still folds.
bool descale_is_decrement(SigMap &sigmap, Cell *reader, const SigSpec &out)
{
  if (reader->type != ID($sub))
    return false;
  if (reader->getParam(ID::A_SIGNED).as_bool() || reader->getParam(ID::B_SIGNED).as_bool())
    return false;
  if (!descale_is_one(reader->getPort(ID::B)))
    return false;
  SigSpec a = sigmap(reader->getPort(ID::A));
  int common = std::min(GetSize(a), GetSize(out));
  if (common == 0 || a.extract(0, common) != out.extract(0, common))
    return false;
  return a.extract_end(common).is_fully_zero();
}

// `out == 0`, in any of the shapes opt_expr leaves behind. Unlike the decrement
// this has to read all of `out`: at full width t + c cannot carry out, so the
// carry is just another bit to test, but a narrower read can wrap into zero.
bool descale_is_zero_test(SigMap &sigmap, Cell *reader, const SigSpec &out)
{
  if (reader->type.in(ID($logic_not), ID($reduce_or), ID($reduce_bool)))
    return sigmap(reader->getPort(ID::A)) == out;
  if (reader->type.in(ID($eq), ID($ne))) {
    if (reader->getParam(ID::A_SIGNED).as_bool() || reader->getParam(ID::B_SIGNED).as_bool())
      return false;
    SigSpec a = sigmap(reader->getPort(ID::A));
    SigSpec b = sigmap(reader->getPort(ID::B));
    if (a == out)
      return b.is_fully_zero();
    if (b == out)
      return a.is_fully_zero();
  }
  return false;
}

// True when every bit of the (already sigmapped) `sig` stays inside the module,
// so this pass is allowed to change what it carries
bool descale_contained(const SigSpec &sig)
{
  for (auto bit : sig)
    if (!bit.wire || bit.wire->port_output || bit.wire->get_bool_attribute(ID::keep))
      return false;
  return true;
}

// Inclusive AND scan of x, so scan[i] = &x[i:0], in ceil(log2(width)) levels
SigSpec descale_and_scan(Cell *cell, const SigSpec &x)
{
  Module *module = cell->module;
  SigSpec scan = x;
  for (int stride = 1; stride < GetSize(x); stride *= 2) {
    int width = GetSize(x) - stride;
    Wire *merged = module->addWire(NEW_ID2_SUFFIX("wnd"), width);
    module->addAnd(NEW_ID2_SUFFIX("wnd"), scan.extract(stride, width),
                   scan.extract(0, width), merged, false, cell->get_src_attribute());
    SigSpec next = scan.extract(0, stride);
    next.append(merged);
    scan = next;
  }
  return scan;
}

// One matched round trip: the shifter is kept and rewired, its readers absorb
// the increment as a window carry, and the increment itself goes away.
struct DescaleRewrite {
  Cell *shr;
  Cell *add;
  SigSpec x;
  SigSpec out;
  vector<Cell *> decs;
  vector<Cell *> zeros;
};

// Unsigned variable right shifts, keyed by the bits they read. Anchoring on the
// shifters first keeps the common case (a design with no round trip) down to one
// walk, with nothing indexed per design bit behind it.
void descale_find_anchors(Module *module, SigMap &sigmap, dict<SigBit, Cell *> &anchors)
{
  vector<Cell *> shifts;
  for (auto cell : module->selected_cells()) {
    if (cell->type != ID($shr) || cell->getParam(ID::A_SIGNED).as_bool())
      continue;

    // A constant amount is folded by -combine, and it makes the window carry
    // constant anyway, so there is no round trip left to break
    if (cell->getPort(ID::B).is_fully_const())
      continue;

    // The rewrite rescales the shifter in place and renames it, which keep forbids
    if (cell->get_bool_attribute(ID::keep))
      continue;

    shifts.push_back(cell);
  }

  // Binding the SigMap is a walk of the module in itself, so leave it unbound
  // for the common case of a module with no variable right shift at all
  if (shifts.empty())
    return;
  sigmap.set(module);

  for (auto cell : shifts)
    for (auto bit : sigmap(cell->getPort(ID::A))) {
      if (!bit.wire)
        continue;
      // Two shifters on one bit means whatever drives it is shared and so cannot
      // be deleted; the null marker rejects both of them
      auto it = anchors.find(bit);
      anchors[bit] = (it == anchors.end() || it->second == cell) ? cell : nullptr;
    }
}

// Increments feeding an anchor: a whole "+1" that is all the shifter reads
void descale_find_candidates(Module *module, SigMap &sigmap, const dict<SigBit, Cell *> &anchors,
                             vector<DescaleRewrite> &candidates)
{
  for (auto cell : module->selected_cells()) {
    if (cell->type != ID($add))
      continue;
    if (cell->getParam(ID::A_SIGNED).as_bool() || cell->getParam(ID::B_SIGNED).as_bool())
      continue;
    // The rewrite deletes the increment outright, which keep forbids
    if (cell->get_bool_attribute(ID::keep))
      continue;

    // Every bit of the sum has to land on one and the same shifter
    SigSpec sum = sigmap(cell->getPort(ID::Y));
    Cell *shr = nullptr;
    bool whole = GetSize(sum) > 0;
    for (auto bit : sum) {
      auto it = anchors.find(bit);
      if (it == anchors.end() || !it->second || (shr && it->second != shr)) {
        whole = false;
        break;
      }
      shr = it->second;
    }
    if (!whole || sigmap(shr->getPort(ID::A)) != sum)
      continue;

    SigSpec a = cell->getPort(ID::A), b = cell->getPort(ID::B);
    SigSpec x = descale_is_one(b) ? a : descale_is_one(a) ? b : SigSpec();
    if (GetSize(x) == 0)
      continue;

    // A truncating increment breaks the carry identity: an all-ones x wraps to
    // 0 instead of carrying into bit width(x)
    if (GetSize(sum) <= GetSize(x))
      continue;

    candidates.push_back({shr, cell, x, sigmap(shr->getPort(ID::Y)), {}, {}});
  }
}

// Readers of just the candidates' own nets: seeding the bits that matter up
// front keeps this to one walk of the module and a pool per candidate bit,
// rather than one per bit in the design.
void descale_index_readers(Module *module, SigMap &sigmap, const vector<DescaleRewrite> &candidates,
                           dict<SigBit, pool<Cell *>> &readers)
{
  for (auto &cand : candidates) {
    for (auto bit : sigmap(cand.add->getPort(ID::Y)))
      readers[bit] = pool<Cell *>();
    for (auto bit : cand.out)
      readers[bit] = pool<Cell *>();
  }

  for (auto cell : module->cells())
    for (auto &conn : cell->connections()) {
      if (cell->output(conn.first))
        continue;
      for (auto bit : sigmap(conn.second)) {
        auto it = readers.find(bit);
        if (it != readers.end())
          it->second.insert(cell);
      }
    }

  // A module-level connection reads bits this pass cannot rewrite; the null
  // marker is a reader no candidate can claim, so those bits are refused
  for (auto &conn : module->connections())
    for (auto bit : sigmap(conn.second)) {
      auto it = readers.find(bit);
      if (it != readers.end())
        it->second.insert(nullptr);
    }
}

int run_descale_shifts(Module *module)
{
  SigMap sigmap; // bound by descale_find_anchors, once it knows it is needed
  dict<SigBit, Cell *> anchors;
  descale_find_anchors(module, sigmap, anchors);
  if (anchors.empty())
    return 0;

  vector<DescaleRewrite> candidates;
  descale_find_candidates(module, sigmap, anchors, candidates);
  if (candidates.empty())
    return 0;

  dict<SigBit, pool<Cell *>> readers;
  descale_index_readers(module, sigmap, candidates, readers);

  vector<DescaleRewrite> rewrites;
  for (auto &cand : candidates) {
    // Both nets end up carrying a different value, so both have to be ours
    SigSpec sum = sigmap(cand.add->getPort(ID::Y));
    if (!descale_contained(sum) || !descale_contained(cand.out))
      continue;

    // The rewrite deletes the increment, so nothing else may be reading it
    pool<Cell *> sharers, consumers;
    for (auto bit : sum)
      for (auto reader : readers.at(bit))
        if (reader != cand.shr)
          sharers.insert(reader);
    if (!sharers.empty())
      continue;

    // Every reader of the shifted result has to be one the carry folds into
    for (auto bit : cand.out)
      for (auto reader : readers.at(bit))
        if (reader != cand.shr)
          consumers.insert(reader);

    bool foldable = true;
    for (auto reader : consumers) {
      // The null marker is a module connection, and an unselected or kept reader
      // is one this pass may not rewire; either way the carry has nowhere to fold
      bool ours = reader && module->selected(reader) && !reader->get_bool_attribute(ID::keep);
      if (ours && descale_is_decrement(sigmap, reader, cand.out))
        cand.decs.push_back(reader);
      else if (ours && descale_is_zero_test(sigmap, reader, cand.out))
        cand.zeros.push_back(reader);
      else {
        foldable = false;
        break;
      }
    }

    // Without a decrement to absorb the carry the increment would just move
    if (!foldable || cand.decs.empty())
      continue;

    log_debug("  %s: descale %s through %s (%d decrement(s), %d zero test(s))\n", log_id(module),
              log_id(cand.add), log_id(cand.shr), GetSize(cand.decs), GetSize(cand.zeros));
    rewrites.push_back(cand);
  }

  for (auto &rewrite : rewrites) {
    Cell *cell = rewrite.shr; // NEW_ID2_SUFFIX names after the shifter
    std::string src = cell->get_src_attribute();

    // Carry out of the discarded window, selected with the data shift amount.
    // Index 0 of the scan is the empty window, so s == 0 reads a hard 1; an
    // amount past width(x) reads a zero bit of the scan and gives 0.
    SigSpec prefix(State::S1);
    prefix.append(descale_and_scan(cell, rewrite.x));
    Wire *carry = module->addWire(NEW_ID2_SUFFIX("carry"));
    module->addShr(NEW_ID2_SUFFIX("carry"), prefix, cell->getPort(ID::B), carry, false, src);

    // The shifter now scales x itself; its readers make up the difference. Its
    // result is a different value than before, so it drives a fresh net rather
    // than leaving a stale meaning on the old name (which formal pairs up).
    Wire *scaled = module->addWire(NEW_ID2_SUFFIX("scaled"), GetSize(rewrite.out));
    cell->setPort(ID::A, rewrite.x);
    cell->setPort(ID::Y, scaled);
    cell->fixup_parameters();

    for (auto dec : rewrite.decs) {
      // The matcher already proved A is the shifter output, zero-extended
      SigSpec operand(scaled);
      operand.extend_u0(GetSize(dec->getPort(ID::A)), false);
      dec->setPort(ID::A, operand);

      // The carry selects rather than borrows: `t - !c` would drag the window
      // test through every result bit, while `c ? t : t - 1` keeps the decrement
      // a constant one and leaves the carry a single-level arc off the shifter
      SigSpec result = dec->getPort(ID::Y);
      Wire *decremented = module->addWire(NEW_ID2_SUFFIX("dec"), GetSize(result));
      dec->setPort(ID::Y, decremented);
      dec->fixup_parameters();
      SigSpec kept(scaled);
      kept.extend_u0(GetSize(result), false);
      module->addMux(NEW_ID2_SUFFIX("dec"), decremented, kept, carry, result, src);
    }
    for (auto zero : rewrite.zeros) {
      // t + carry is zero exactly when neither part is, so the carry can just
      // ride along as a new top bit of the tested word
      IdString port = sigmap(zero->getPort(ID::A)) == rewrite.out ? ID::A : ID::B;
      SigSpec tested(scaled);
      tested.append(carry);
      zero->setPort(port, tested);
      zero->fixup_parameters();
    }

    // equiv_make pairs gold and gate cells by name and then asserts their inputs
    // equivalent, so every cell that now sees a different value has to be renamed
    // or formal reports the intended difference as a failure
    for (const vector<Cell *> &group : {vector<Cell *>{cell}, rewrite.decs, rewrite.zeros})
      for (Cell *touched : group)
        module->rename(touched, module->uniquify(touched->name.str() + "_descale"));

    module->remove(rewrite.add);
    did_something = true;
  }

  return GetSize(rewrites);
}

#include "passes/silimate/peepopt_shift_pm.h"
#include "passes/silimate/peepopt_sink_pm.h"

struct OptShiftPass : public Pass {
  OptShiftPass() : Pass("opt_shift", "shift optimizations: combine, expand, sink and fuse") { }
  void help() override
  {
    //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
    log("\n");
    log("    opt_shift [options] [selection]\n");
    log("\n");
    log("This pass performs shift optimizations.\n");
    log("\n");
    log("  -combine\n");
    log("      Combine nested shift operations (works with all\n");
    log("      combinations of $shl/$sshl and $shr/$sshr):\n");
    log("        (a <</<< b) <</<< c    ===>  a <</<< (b + c)\n");
    log("        (a >>>/>> b) >>>/>> c  ===>  a >>>/>> (b + c)\n");
    log("        (a <</<< b) >>>/>> c   ===>  a <</<< (b - c)\n");
    log("        (a >>>/>> b) <</<< c   ===>  a >>>/>> (b - c)\n");
    log("      Result uses the inner shift's type.\n");
    log("\n");
    log("  -expand\n");
    log("      Expand shifts across binary operations:\n");
    log("        (a OP b) << c    ===>  (a << c) OP (b << c)\n");
    log("        (a OP b) >> c    ===>  (a >> c) OP (b >> c)\n");
    log("        where OP in {$and, $or, $xor, $add, $sub}\n");
    log("\n");
    log("  -sink\n");
    log("      Sink an add through a left shift, so the adder leaves the\n");
    log("      shifter output and can merge with the arithmetic feeding it:\n");
    log("        (x << s) + z    ===>  ((x + (z >> s)) << s) | (z & ~(~0 << s))\n");
    log("      Requires a provable nonzero minimum for s, which is what makes\n");
    log("      (z >> s) narrower than z. This is the inverse of -expand on\n");
    log("      $add, so the two must not be requested together.\n");
    log("\n");
    log("  -fuse\n");
    log("      Fuse a modular gather with the variable left shift feeding it,\n");
    log("      which -combine cannot do because the gather rotates its table:\n");
    log("        pad_M(x << b)[(t + a + r) %% M]\n");
    log("          ===>  pad_M(x & (~0 >> b))[(t + a + r - b) %% M]\n");
    log("      Masking x replaces the zero fill the rotate would wrap around,\n");
    log("      so two barrels on the data path become one plus a mask that\n");
    log("      depends only on b. Only fires when the gather cannot shift past\n");
    log("      its own source, where it zero-fills but a rotate would wrap.\n");
    log("\n");
    log("  -max_fuse_bits n\n");
    log("      refuse a -fuse rewrite whose repeated source would exceed n\n");
    log("      bits (default 4096).\n");
    log("\n");
    log("  -push\n");
    log("      Push a variable right shift through a per-bit merge, so it can\n");
    log("      compose with the barrel feeding one side of that merge, which\n");
    log("      -combine cannot do with the merge sitting between them:\n");
    log("        ((S ? b : a) >> s)[j]\n");
    log("          ===>  (S >> s)[j] ? (b >> s)[j] : (a >> s)[j]\n");
    log("        where a[i] = (x >> g)[i - k], so (a >> s) = {x, k'0} >> (g + s)\n");
    log("      Two barrels on the data path become one; b and S pick up barrels\n");
    log("      of their own, which is why this only fires when a side really is\n");
    log("      a variable shift, and why the deepest barrel goes first when\n");
    log("      several match. The composed source is wider than a, so the\n");
    log("      select is oriented to pick the composed side on a 1: past the\n");
    log("      top of the merge, where a >> s would zero-fill, the mux then\n");
    log("      reads b's fill instead of more of x. Output bits below k keep\n");
    log("      the merge, since the composed source is pad rather than a there.\n");
    log("\n");
    log("  -max_push_offset n\n");
    log("      refuse a -push rewrite whose merge sits more than n bits above\n");
    log("      the inner shift, since each of those bits keeps a merge\n");
    log("      (default 8).\n");
    log("\n");
    log("  -descale\n");
    log("      Collapse a scale-down round trip around a variable right shift,\n");
    log("      so one carry chain is left instead of two bracketing the shifter:\n");
    log("        ((x + 1) >> s) - 1  ===>  c ? (x >> s) : (x >> s) - 1\n");
    log("      where c = &x[s-1:0]. Writing x = t*2^s + r, the shift throws r\n");
    log("      away, so all the increment can still contribute is its carry out\n");
    log("      of that window, which is c (vacuously true for s == 0). The carry\n");
    log("      lands on a select rather than the decrement's borrow input, which\n");
    log("      would otherwise drag the window test through every result bit, and\n");
    log("      the test itself is a log-depth AND scan beside the shifter.\n");
    log("      The increment must not truncate: an all-ones x has to carry into\n");
    log("      bit width(x) rather than wrap to zero. Only readers the carry can\n");
    log("      fold into are accepted, which is `- 1` and `== 0`.\n");
    log("\n");
    log("  -max_iters n\n");
    log("      max number of pass iterations to run.\n");
    log("\n");
    log("If none of -combine, -expand, -sink, -fuse, -push or -descale is given,\n");
    log("combine and expand are run.\n");
    log("\n");
  }
  void execute(std::vector<std::string> args, RTLIL::Design *design) override
  {
    log_header(design, "Executing OPT_SHIFT pass (shift optimizations).\n");

    bool run_combine = false;
    bool run_expand = false;
    bool run_sink = false;
    bool run_fuse = false;
    bool run_push = false;
    bool run_descale = false;
    int max_fuse_bits = 4096;
    int max_push_offset = 8;
    int max_iters = 10000;
    int descale_count = 0;

    size_t argidx;
    for (argidx = 1; argidx < args.size(); argidx++) {
      if (args[argidx] == "-combine") {
        run_combine = true;
        continue;
      }
      if (args[argidx] == "-expand") {
        run_expand = true;
        continue;
      }
      if (args[argidx] == "-sink") {
        run_sink = true;
        continue;
      }
      if (args[argidx] == "-fuse") {
        run_fuse = true;
        continue;
      }
      if (args[argidx] == "-push") {
        run_push = true;
        continue;
      }
      if (args[argidx] == "-descale") {
        run_descale = true;
        continue;
      }
      if (args[argidx] == "-max_fuse_bits" && argidx + 1 < args.size()) {
        max_fuse_bits = std::stoi(args[++argidx]);
        continue;
      }
      if (args[argidx] == "-max_push_offset" && argidx + 1 < args.size()) {
        max_push_offset = std::stoi(args[++argidx]);
        continue;
      }
      if (args[argidx] == "-max_iters" && argidx + 1 < args.size()) {
        max_iters = std::stoi(args[++argidx]);
        continue;
      }
      break;
    }
    extra_args(args, argidx, design);

    if (!run_combine && !run_expand && !run_sink && !run_push && !run_fuse && !run_descale) {
      run_combine = true;
      run_expand = true;
    }

    // -expand undoes -sink on $add, so they would ping-pong until max_iters
    if (run_expand && run_sink)
      log_cmd_error("opt_shift: -expand and -sink are inverses, pick one.\n");

    int total_fused = 0;
    int total_pushed = 0;
    for (auto module : design->selected_modules())
    {
      // A process can read the nets -descale redirects, and it is not in the
      // cell graph, so that reader can neither be seen nor rewritten. Checked
      // once per module so the warning does not repeat over the iterations.
      bool descale_module = run_descale && !module->has_processes_warn();
      did_something = true;
      for (int i = 0; did_something && i < max_iters; i++)
      {
        did_something = false;
        if (run_combine || run_expand) {
          peepopt_shift_pm pm(module);
          pm.setup(module->selected_cells());
          if (run_combine)
            pm.run_combine_shifts();
          if (run_expand)
            pm.run_expand_shifts();
        }
        // Indexing the drivers and every $add is only worth it once we know a
        // variable-amount shifter exists; most modules have none and skip it
        if (run_sink && has_variable_shift(module, {ID($shl)})) {
          sink_index_module(module);
          peepopt_sink_pm pm(module);
          pm.setup(module->selected_cells());
          pm.run_sink_shifts();
        }
        // Same pre-filter: a gather only fuses with a variable-amount shifter
        if (run_fuse && has_variable_shift(module, {ID($shl)})) {
          GatherFuser fuser(module, max_fuse_bits);
          did_something |= fuser.run();
          total_fused += fuser.fused;
        }
        // Same pre-filter: a merge only pushes onto a variable-amount shifter
        if (run_push && has_variable_shift(module, {ID($shr)})) {
          MergePusher pusher(module, max_push_offset);
          did_something |= pusher.run();
          total_pushed += pusher.pushed;
        }
        if (descale_module)
          descale_count += run_descale_shifts(module);
      }
    }

    if (run_fuse)
      log("Fused %d gather(s) with the shift feeding them.\n", total_fused);
    if (run_push)
      log("Pushed %d shift(s) through a merge onto the shift below it.\n", total_pushed);
    if (run_descale)
      log("Collapsed %d scale-down round trip(s) into window-carry logic.\n", descale_count);
  }
} OptShiftPass;

PRIVATE_NAMESPACE_END
