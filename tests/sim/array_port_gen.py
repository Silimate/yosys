"""Generate the dumps replayed by array_port_*.ys against array_port.v.

A simulator has several ways to dump one array port, and sim must bind the element wires
Verific splits it into (`\\coeffs[-1]`, `\\grid[1][0]`) from each of them:

  elements   one vector per element, index in the name       coeffs[-1] [2:0]
  ranges     one vector per element, index in the range       grid [1][-1][3:0]
  scopes     a scope per outer index, element named by index  scope grid[1]: [-1] [3:0]
  bits       the array flattened, one 1-bit var per bit       coeffs [8] .. coeffs [0]
  vector     the array flattened into one vector              coeffs [8:0]
  rows       each outer element flattened (2-D only)          grid[1] [11:0], grid[0] [k]

Flattened shapes pack elements the SystemVerilog way: the left declared bound of every
dimension is most significant, so `coeffs [0:-2]` puts [-2] in the low bits and `offs [1:3]`
puts [3] there. The dumped outputs are those same packings, so `sim -sim-cmp` catches an element
bound to the wrong bits as well as one left unbound.

Every value is written out at three timestamps with distinct element values in each.

Run `python3 array_port_gen.py` in this directory after changing this file.
"""

import itertools

STEPS = 3


def ids():
    """VCD identifier codes."""
    for i in itertools.count():
        yield chr(33 + i % 94) * (1 + i // 94)


class Array:
    """An array port: element width and declared (left, right) bounds per dimension."""

    def __init__(self, name, width, dims):
        self.name, self.width, self.dims = name, width, dims

    def indices(self):
        """Element index tuples in declaration order, most significant element first."""
        ranges = [range(l, r - 1, -1) if l >= r else range(l, r + 1) for l, r in self.dims]
        return list(itertools.product(*ranges))

    def value(self, step, ordinal):
        """Distinct element values within a step, changing between steps."""
        return ((ordinal + 1) * 3 + step * 5) % (1 << self.width)

    def packed(self, step, prefix=()):
        """Bit string, MSB first, of the elements whose leading indices are `prefix`."""
        return "".join(format(self.value(step, n), f"0{self.width}b")
                       for n, idx in enumerate(self.indices()) if idx[:len(prefix)] == prefix)

    def element(self, step, idx):
        """Bit string of one element."""
        return format(self.value(step, self.indices().index(idx)), f"0{self.width}b")


COEFFS = Array("coeffs", 3, [(0, -2)])
OFFS = Array("offs", 2, [(1, 3)])
ASC = Array("asc", 4, [(-2, 0)])
GRID = Array("grid", 4, [(1, 0), (-1, 1)])


def idx_name(idx):
    return "".join(f"[{i}]" for i in idx)


class Dump:
    """Collects `$var`s under tb.dut and the value each takes at every step."""

    def __init__(self):
        self.codes = ids()
        self.decls = []  # (scope path under dut, var line)
        self.values = []  # (code, width, step -> bit string)

    def var(self, name, width, value, scope=None, vrange=None):
        code = next(self.codes)
        vrange = vrange if vrange is not None else (f"[{width - 1}:0]" if width > 1 else "")
        self.decls.append((scope, f"$var wire {width} {code} {name} {vrange} $end".replace("  ", " ")))
        self.values.append((code, width, value))

    def write(self, path):
        lines = ["$timescale 1ns $end", "$scope module tb $end"]
        lines += [decl for scope, decl in self.decls if scope == "tb"]
        lines.append("$scope module dut $end")
        open_scope = None
        for scope, decl in self.decls:
            if scope == "tb":
                continue
            if scope != open_scope:
                if open_scope is not None:
                    lines.append("$upscope $end")
                if scope is not None:
                    lines.append(f"$scope fork {scope} $end")
                open_scope = scope
            lines.append(decl)
        if open_scope is not None:
            lines.append("$upscope $end")
        lines += ["$upscope $end", "$upscope $end", "$enddefinitions $end"]
        for step in range(STEPS):
            lines.append(f"#{step * 10}")
            for code, width, value in self.values:
                bits = value(step)
                lines.append(f"b{bits} {code}" if width > 1 else f"{bits}{code}")
        lines.append(f"#{STEPS * 10}")
        with open(path, "w", encoding="utf-8") as f:
            f.write("\n".join(lines) + "\n")


def output(dump, name, arr):
    """The module output that packs `arr`, as recorded by the simulator."""
    width = arr.width * len(arr.indices())
    dump.var(name, width, lambda s: arr.packed(s))


def elements(dump, arr, ranges=False):
    for idx in arr.indices():
        value = lambda s, idx=idx: arr.element(s, idx)
        if ranges:
            dump.var(arr.name, arr.width, value, vrange=f"{idx_name(idx)}[{arr.width - 1}:0]")
        else:
            dump.var(arr.name + idx_name(idx), arr.width, value)


def bits(dump, arr, prefix=()):
    name = arr.name + idx_name(prefix)
    for k in reversed(range(len(arr.packed(0, prefix)))):
        dump.var(name, 1, lambda s, k=k: arr.packed(s, prefix)[-1 - k], vrange=f"[{k}]")


def vector(dump, arr, prefix=()):
    dump.var(arr.name + idx_name(prefix), len(arr.packed(0, prefix)), lambda s: arr.packed(s, prefix))


def dump_1d(path, shape):
    dump = Dump()
    for arr in (COEFFS, OFFS, ASC):
        shape(dump, arr)
    for name, arr in (("coeffs_q", COEFFS), ("offs_q", OFFS), ("asc_q", ASC)):
        output(dump, name, arr)
    dump.write(path)


def dump_2d(path, shape):
    dump = Dump()
    shape(dump, GRID)
    output(dump, "grid_q", GRID)
    dump.write(path)


def scopes(dump, arr):
    for idx in arr.indices():
        dump.var(idx_name(idx[1:]), arr.width, lambda s, idx=idx: arr.element(s, idx),
                 scope=arr.name + idx_name(idx[:1]))


def rows(dump, arr):
    # Mixed on purpose: the first row as one vector, the second as 1-bit vars
    vector(dump, arr, (1,))
    bits(dump, arr, (0,))


def controls(path):
    dump = Dump()
    vec = lambda s: format((0x5A + 17 * s) & 0xFF, "08b")
    bitv = lambda s: format((1 + s) % 4, "02b")
    din = lambda s: format((0xC3 ^ (s * 0x11)) & 0xFF, "08b")  # din[1], bits 15..8 of the dump
    din0 = lambda s: "10010110"  # din[0], not a port of the module
    src = lambda s: format((0x96 + 29 * s) & 0xFF, "08b")
    dump.var("vec", 8, vec)
    dump.var("bits", 1, lambda s: bitv(s)[0], vrange="[1]")
    dump.var("bits", 1, lambda s: bitv(s)[1], vrange="[0]")
    for k in range(16):
        dump.var(f"din[{k}]", 1, lambda s, k=k: (din(s) + din0(s))[15 - k], vrange="")
    dump.var("src", 8, src, scope="tb")
    dump.var("ctl_q", 26, lambda s: vec(s) + bitv(s) + din(s) + "1010" + src(s)[2:6])
    dump.write(path)


def main():
    dump_1d("array_port_1d_elements.vcd", elements)
    dump_1d("array_port_1d_bits.vcd", bits)
    dump_1d("array_port_1d_vector.vcd", vector)
    dump_2d("array_port_2d_elements.vcd", elements)
    dump_2d("array_port_2d_ranges.vcd", lambda d, a: elements(d, a, ranges=True))
    dump_2d("array_port_2d_scopes.vcd", scopes)
    dump_2d("array_port_2d_bits.vcd", bits)
    dump_2d("array_port_2d_vector.vcd", vector)
    dump_2d("array_port_2d_rows.vcd", rows)
    controls("array_port_controls.vcd")


if __name__ == "__main__":
    main()
