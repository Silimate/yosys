#!/usr/bin/env bash
#
# Throwaway debug helper: render only the neighborhood that changed across an
# opt_retime move. Same CLI as retime_debug.sh, same side-loading rules (*.sh
# is not a test target here), and the same "delete it when it stops helping"
# status. Use this instead of retime_debug.sh when the design is too large for
# a full-netlist picture.
#
# usage: ./retime_debug_diff.sh <design.v> <top> <opt_retime args...>
#
#   ./retime_debug_diff.sh opt_retime_add.v retime_add -flop fa -cut a0 -forward
#
# A bare "+" runs several moves in one before/after pair, same as
# retime_debug.sh.
#
# env:
#   YOSYS  yosys binary            (default ../../build/yosys)
#   OUT    output directory        (default /tmp/retime_debug_diff/<top>)
#   CLEAN  run opt_clean on the    (default 0; see retime_debug.sh)
#          retimed netlist first
#   PRE    yosys commands to run  (default none; see retime_debug.sh)
#          before the snapshot
#   REFUSE expect the move to be   (default 0. A refused move leaves no after
#          refused                  netlist, so there is no diff to seed the
#                                   neighborhood from: the cells the move named
#                                   are used instead, the flop that could not
#                                   move and the cut it could not reach. Only
#                                   the before picture is drawn and the reason
#                                   lands in <OUT>/refusal.txt)
#   HOPS   neighborhood radius     (default 3)
#   CONE   1: expand only through  (default 1, so a changed flop does not
#          combinational cells      pull in every register on the same clock)
#          0: hop through anything
#          except CLK/C/EN ports
#   NETLISTSVG, NETLISTSVG_DIR     same as retime_debug.sh
#
# The flop named by -flop is the same cell on both sides; it just moved. Color
# it red in the before picture (leaving) and green in the after picture
# (arriving). Flops the move merged away are collateral, orange in before.
# Truly new wires (a _retimed net on a resize) are green in after.
#
# Writes <OUT>/{before,after}.{il,json,svg,png}, {before,after}_full.json of
# the whole design (for register counts, not pictures), {before,after}_show
# graphviz renderings of the neighborhood, and seeds.txt listing the cells
# and wires the RTLIL diff considered changed.

set -euo pipefail

if [ $# -lt 3 ]; then
	sed -n '3,21p' "$0"
	exit 1
fi

design=$1
top=$2
shift 2

retime=""
args=""
flops=""
cuts=""
prev=""
for arg in "$@"; do
	if [ "$arg" = "+" ]; then
		retime="$retime opt_retime$args;"
		args=""
	else
		args="$args $arg"
	fi
	if [ "$prev" = "-flop" ]; then
		flops="$flops $arg"
	fi
	# Only REFUSE=1 needs these, since a move that ran is seeded from its diff.
	if [ "$prev" = "-cut" ]; then
		cuts="$cuts,$arg"
	fi
	prev=$arg
done
retime="$retime opt_retime$args;"
flops=${flops# }
cuts=${cuts#,}

yosys=${YOSYS:-../../build/yosys}
out=${OUT:-/tmp/retime_debug_diff/$top}
clean=${CLEAN:-0}
pre=${PRE:-}
hops=${HOPS:-3}
cone=${CONE:-1}
refuse=${REFUSE:-0}
nlsvg_dir=${NETLISTSVG_DIR:-/tmp/retime_debug_netlistsvg}

if [ ! -x "$yosys" ]; then
	echo "no yosys at $yosys, set YOSYS=<path>" >&2
	exit 1
fi

mkdir -p "$out"
out=$(cd "$out" && pwd)
rm -f "$out"/before.* "$out"/after.* "$out"/before_show.* "$out"/after_show.* \
	"$out"/before_full.json "$out"/after_full.json "$out"/seeds.txt "$out"/seeds.ys \
	"$out"/diff_colors.json "$out"/refusal.txt "$out"/yosys.log

clean_cmd=""
[ "$clean" = "1" ] && clean_cmd="opt_clean"

# One yosys run, so before and after come from the same elaboration. The IL is
# sorted so a text compare is a structural compare, not a hash-order shuffle.
# Full JSON is only for counting registers later; it is never drawn.
#
# Kept on disk rather than piped for the same reasons as in retime_debug.sh: a
# refusal reports itself only in the log, and pipefail would treat the failure
# REFUSE=1 is asking for as a failure of this script.
set +e
"$yosys" -p "
	read_verilog -icells $design
	hierarchy -top $top
	check -assert
	$pre
	write_rtlil -sort $out/before.il
	write_json $out/before_full.json
	$retime
	check -assert
	$clean_cmd
	write_rtlil -sort $out/after.il
	write_json $out/after_full.json
" >"$out/yosys.log" 2>&1
rc=$?
set -e

sed -n '/Executing OPT_RETIME/,/^$/p' "$out/yosys.log"

if [ "$refuse" = "1" ]; then
	if [ "$rc" -eq 0 ]; then
		echo "REFUSE=1 but the move succeeded, so this entry is stale" >&2
		exit 1
	fi
	grep -m1 '^ERROR: ' "$out/yosys.log" | sed 's/^ERROR: //' >"$out/refusal.txt" || true
	echo "refused: $(cat "$out/refusal.txt")"
elif [ "$rc" -ne 0 ]; then
	cat "$out/yosys.log" >&2
	exit "$rc"
fi

python3 - "$out/before.il" "$out/after.il" "$out/seeds.txt" "$out/seeds.ys" \
	"$out/diff_colors.json" "$hops" "$cone" "$refuse" "$cuts" $flops <<'PY'
import json, sys

before_il, after_il, seeds_txt, seeds_ys, colors_json, hops, cone, refuse, cuts_csv = sys.argv[1:10]
moved = list(dict.fromkeys(sys.argv[10:]))
hops = int(hops)
cone = cone == "1"
refuse = refuse == "1"
cuts = [c for c in cuts_csv.split(",") if c]

EMPTY = "n:$__diff_empty__"
FF_TYPES = ("$dff", "$dffe", "$adff", "$sdff", "$adffe", "$sdffe", "$aldff", "$dlatch")


def unesc(name):
    return name[1:] if name.startswith("\\") else name


def is_ff(cell_text):
    typ = unesc(cell_text.split()[1])
    return typ in FF_TYPES or typ.startswith("$_DFF") or typ.startswith("$_SDFF") or typ.startswith("$_DLATCH")


def parse(path):
    cells, wires, assigns = {}, {}, {}
    in_module = False
    in_cell = False
    cell_name = None
    cell_lines = []
    with open(path) as f:
        for line in f:
            s = line.strip()
            if not in_module:
                if s.startswith("module "):
                    in_module = True
                continue
            if in_cell:
                if s.startswith("parameter ") or s.startswith("connect "):
                    cell_lines.append(s)
                elif s == "end":
                    cells[cell_name] = "\n".join(cell_lines)
                    in_cell = False
                continue
            if s == "end":
                in_module = False
                continue
            if s.startswith("cell "):
                parts = s.split()
                cell_name = unesc(parts[-1])
                cell_lines = [s]
                in_cell = True
                continue
            if s.startswith("wire "):
                wires[unesc(s.split()[-1])] = s
                continue
            if s.startswith("connect "):
                assigns[unesc(s.split()[1])] = s
    return cells, wires, assigns


def classify(a, b):
    added = sorted(set(b) - set(a))
    deleted = sorted(set(a) - set(b))
    changed = sorted(n for n in set(a) & set(b) if a[n] != b[n])
    return added, deleted, changed


def sel(kind_cells, kind_wires=()):
    parts = [f"c:{n}" for n in kind_cells] + [f"w:{n}" for n in kind_wires]
    return " ".join(parts) if parts else EMPTY


ba, wa, aa = parse(before_il)
if refuse:
    # A refused move changed nothing, so there is no diff to seed from. The
    # cells the move named stand in for it: the flop that could not move and
    # the cut it could not reach, which between them are what the picture is
    # meant to explain.
    moved = [n for n in moved if n in ba]
    seed_cells = sorted(set(moved) | {c for c in cuts if c in ba})
    seed_wires = []
    add_c = del_c = ch_c = add_w = del_w = ch_w = collateral = []
else:
    bb, wb, ab = parse(after_il)
    add_c, del_c, ch_c = classify(ba, bb)
    add_w, del_w, ch_w = classify({**wa, **aa}, {**wb, **ab})
    seed_cells = sorted(set(add_c) | set(del_c) | set(ch_c))
    seed_wires = sorted(set(add_w) | set(del_w) | set(ch_w))
    moved = [n for n in moved if n in ba or n in bb]
    collateral = [n for n in del_c if n not in moved and is_ff(ba[n])]

with open(seeds_txt, "w") as f:
    f.write("cells: " + " ".join(seed_cells) + "\n")
    f.write("wires: " + " ".join(seed_wires) + "\n")
    f.write("moved: " + " ".join(moved) + "\n")
    f.write("collateral: " + " ".join(collateral) + "\n")
    f.write("added_cells: " + " ".join(add_c) + "\n")
    f.write("deleted_cells: " + " ".join(del_c) + "\n")
    f.write("changed_cells: " + " ".join(ch_c) + "\n")
    f.write("added_wires: " + " ".join(add_w) + "\n")
    f.write("deleted_wires: " + " ".join(del_w) + "\n")

with open(colors_json, "w") as f:
    json.dump({"moved": moved, "collateral": collateral, "added": add_c + add_w}, f)

if not seed_cells and not seed_wires:
    open(seeds_ys, "w").close()
    print("seeds: none (no cells named)" if refuse else "seeds: none (no structural RTLIL diff)")
    sys.exit(0)

if refuse:
    # A refused move has no diff to sit at the middle of a neighborhood, and
    # the interesting thing about it is usually the operand the move could not
    # merge, which a register-bounded cone leaves out: %cie/%coe only consider
    # combinatorial cells, so a sibling flop feeding the cut would appear as
    # nothing but the wire it drives. Show the whole module instead and let the
    # colour pick out the flop that could not move.
    view = "select -set view *"
elif hops <= 0:
    view = "select -set view @seed"
elif cone:
    view = f"select -set view @seed %cie{hops} @seed %coe{hops} %u"
else:
    # CLK/C/EN are shared across the chip; hopping through them is how a
    # one-flop diff becomes a picture of every register.
    view = f"select -set view @seed %x{hops}:-[CLK,C,EN]"

with open(seeds_ys, "w") as f:
    f.write(f"select -set seed {sel(seed_cells, seed_wires)}\n")
    f.write(f"select -set moved {sel(moved)}\n")
    f.write(f"select -set collateral {sel(collateral)}\n")
    f.write(f"select -set added {sel(add_c, add_w)}\n")
    f.write(view + "\n")

print("seeds: %d cell(s), %d wire(s)" % (len(seed_cells), len(seed_wires)))
print("  moved:       " + (" ".join(moved) or "(none)"))
print("  collateral:  " + (" ".join(collateral) or "(none)"))
print("  added:       " + (" ".join(add_c + add_w) or "(none)"))
PY

if [ ! -s "$out/seeds.ys" ]; then
	echo "nothing to draw" >&2
	echo
	echo "wrote:"
	for f in "$out"/before.il "$out"/after.il "$out"/seeds.txt; do
		[ -f "$f" ] && echo "  $f"
	done
	exit 0
fi

have_dot=0
command -v dot >/dev/null && have_dot=1

nlsvg=${NETLISTSVG:-}
if [ -z "$nlsvg" ]; then
	nlsvg=$nlsvg_dir/node_modules/.bin/netlistsvg
	if [ ! -x "$nlsvg" ]; then
		echo "installing netlistsvg into $nlsvg_dir (one time)"
		npm install --silent --prefix "$nlsvg_dir" netlistsvg >/dev/null
	fi
fi

# netlistsvg has no color attribute. It stamps class="cell_<name>" on the
# body of each cell, so a small CSS patch after it runs is enough. The same
# cell (the -flop) is red before and green after; merged-away flops are orange.
colorize_svg() {
	python3 - "$1" "$2" "$out/diff_colors.json" <<'PY'
import json, re, sys

svg_path, stage, colors_path = sys.argv[1:4]
colors = json.load(open(colors_path))
moved = colors.get("moved") or []
collateral = colors.get("collateral") or []
added = colors.get("added") or []


def css_ident(name):
    return "cell_" + re.sub(r"([^A-Za-z0-9_-])", lambda m: "\\%x " % ord(m.group(1)), name)


def rules(names, stroke, fill):
    out = []
    for name in names:
        ident = css_ident(name)
        out.append("rect.%s, path.%s, circle.%s { stroke: %s; fill: %s; }" % (ident, ident, ident, stroke, fill))
        out.append("line.%s { stroke: %s; }" % (ident, stroke))
    return out


if stage == "before":
    css = rules(moved, "#c62828", "#ffcdd2") + rules(collateral, "#ef6c00", "#ffe0b2")
else:
    css = rules(moved, "#2e7d32", "#c8e6c9") + rules(added, "#2e7d32", "#c8e6c9")
if not css:
    sys.exit(0)
text = open(svg_path).read()
gt = text.find(">")
if gt < 0:
    sys.exit(0)
open(svg_path, "w").write(text[: gt + 1] + "\n<style>\n" + "\n".join(css) + "\n</style>\n" + text[gt + 1 :])
PY
}

# Same selection on both sides: objects that exist on only one side simply
# fail to match there. submod copies the neighborhood into its own module so
# write_json is a complete netlist rather than a ragged -selected fragment.
# show runs first, because submod would add a second module and show -format
# svg refuses that.
render() {
	local stage=$1
	local ys=$out/render_$stage.ys
	{
		echo "read_rtlil $out/$stage.il"
		echo "cd $top"
		cat "$out/seeds.ys"
		if [ "$have_dot" = 1 ]; then
			if [ "$stage" = before ]; then
				echo "show -format svg -prefix $out/${stage}_show -notitle -width -signed -color crimson @moved -color orange @collateral @view"
			else
				echo "show -format svg -prefix $out/${stage}_show -notitle -width -signed -color forestgreen @moved -color forestgreen @added @view"
			fi
		fi
		echo "submod -copy -noclean -name diffview @view"
		echo "select -clear"
		echo "select diffview"
		echo "write_json -selected $out/$stage.json"
	} >"$ys"
	"$yosys" -q -s "$ys"
	if [ -x "$nlsvg" ] && [ -f "$out/$stage.json" ]; then
		"$nlsvg" "$out/$stage.json" -o "$out/$stage.svg" 2>/dev/null || true
		[ -f "$out/$stage.svg" ] && colorize_svg "$out/$stage.svg" "$stage"
	fi
	if command -v rsvg-convert >/dev/null; then
		[ -f "$out/$stage.svg" ] &&
			rsvg-convert -z 2 -b white -o "$out/$stage.png" "$out/$stage.svg"
		[ -f "$out/${stage}_show.svg" ] &&
			rsvg-convert -z 1.5 -b white -o "$out/${stage}_show.png" "$out/${stage}_show.svg"
	fi
}

if [ "$have_dot" = 0 ]; then
	echo "no graphviz dot in PATH, skipping the width-annotated view" >&2
fi

render before
# A refused move wrote no after.il, so there is only one side to render.
[ "$refuse" = "1" ] || render after

echo
echo "wrote:"
# An if rather than a && so that a glob matching nothing, which is every after
# glob once a move has been refused, does not become this script's exit status.
for f in "$out"/before.* "$out"/after.* "$out"/before_show.* "$out"/after_show.* \
	"$out"/before_full.json "$out"/after_full.json "$out"/seeds.txt; do
	if [ -f "$f" ]; then
		echo "  $f"
	fi
done
