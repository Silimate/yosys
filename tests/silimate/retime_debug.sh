#!/usr/bin/env bash
#
# Throwaway debug helper: render a netlist before and after an opt_retime move.
# Deliberately side-loaded: generate_mk.py here passes only -y and -t, so *.ys
# and *.tcl are test targets but *.sh is not, and this reads the designs without
# touching them or any .ys script. Delete it whenever it stops being useful.
#
# usage: ./retime_debug.sh <design.v> <top> <opt_retime args...>
#
#   ./retime_debug.sh opt_retime_add.v retime_add -flop fa -cut a0 -forward
#   ./retime_debug.sh opt_retime_add.v retime_add -flop fa -cut a1 -forward
#
# A bare "+" runs several moves in one before/after pair:
#
#   ./retime_debug.sh opt_retime_cmp.v retime_cmp \
#       -flop fc -cut r_or -forward + -flop fa -cut g0 -forward
#
# env:
#   YOSYS  yosys binary            (default ../../build/yosys)
#   OUT    output directory        (default /tmp/retime_debug/<top>)
#   CLEAN  run opt_clean on the    (default 0, so the picture is exactly what
#          retimed netlist first    the pass produced. CLEAN=1 tidies the nets
#                                   a merge leaves dangling, but it also
#                                   absorbs $buf cells, which makes it look
#                                   like retiming deleted them)
#   NETLISTSVG      path to a netlistsvg binary, if you already have one
#   NETLISTSVG_DIR  where to install it otherwise
#                   (default /tmp/retime_debug_netlistsvg, installed once)
#
# Writes <OUT>/{before,after}.{json,svg,png} plus {before,after}_show.{svg,png}.
# The json is what yosys sees and the plain svg/png are netlistsvg renderings of
# it. The _show pair comes from yosys' own "show -width" instead, which is the
# only one of the two that labels bus widths: netlistsvg has no such feature to
# switch on, its ELK edges never get labels at all. That view also names cell
# ports, so it is the one to read when a move lands on the wrong port; the
# netlistsvg one is easier to follow for the shape of a path. Needs graphviz
# dot, and is quietly skipped when that is missing.

set -euo pipefail

if [ $# -lt 3 ]; then
	sed -n '3,21p' "$0"
	exit 1
fi

design=$1
top=$2
shift 2

# A bare "+" separates several moves, for cuts that only become legal in
# sequence: opt_retime_cmp.v cannot move across g0 until something has put a
# register on g0.B.
retime=""
args=""
for arg in "$@"; do
	if [ "$arg" = "+" ]; then
		retime="$retime opt_retime$args;"
		args=""
	else
		args="$args $arg"
	fi
done
retime="$retime opt_retime$args;"

yosys=${YOSYS:-../../build/yosys}
out=${OUT:-/tmp/retime_debug/$top}
clean=${CLEAN:-0}
nlsvg_dir=${NETLISTSVG_DIR:-/tmp/retime_debug_netlistsvg}

if [ ! -x "$yosys" ]; then
	echo "no yosys at $yosys, set YOSYS=<path>" >&2
	exit 1
fi

mkdir -p "$out"
rm -f "$out"/before.* "$out"/after.* "$out"/before_show.* "$out"/after_show.*

clean_cmd=""
[ "$clean" = "1" ] && clean_cmd="opt_clean"

# -width is the whole reason this view exists; -signed marks a signed A or B,
# which is worth seeing next to a comparator. Given -format and -prefix, show
# writes the file and does not launch a viewer, so this stays headless.
show_before=""
show_after=""
if command -v dot >/dev/null; then
	show_before="show -format svg -prefix $out/before_show -notitle -width -signed"
	show_after="show -format svg -prefix $out/after_show -notitle -width -signed"
else
	echo "no graphviz dot in PATH, skipping the width-annotated view" >&2
fi

# One yosys run, so before and after come from the same elaboration.
"$yosys" -p "
	read_verilog -icells $design
	hierarchy -top $top
	check -assert
	write_json $out/before.json
	$show_before
	$retime
	check -assert
	$clean_cmd
	write_json $out/after.json
	$show_after
" | sed -n '/Executing OPT_RETIME/,/^$/p'

# netlistsvg is installed once into a scratch prefix rather than run through
# npx, which re-resolves the package on every call and dominated the runtime of
# retime_debug_all.sh. Nothing is added to the repo or installed globally.
nlsvg=${NETLISTSVG:-}
if [ -z "$nlsvg" ]; then
	nlsvg=$nlsvg_dir/node_modules/.bin/netlistsvg
	if [ ! -x "$nlsvg" ]; then
		echo "installing netlistsvg into $nlsvg_dir (one time)"
		npm install --silent --prefix "$nlsvg_dir" netlistsvg >/dev/null
	fi
fi

for stage in before after; do
	"$nlsvg" "$out/$stage.json" -o "$out/$stage.svg" 2>/dev/null
done

# show already emitted its own svg, so both views just need rasterizing. The
# graphviz one is denser, so it gets less magnification.
if command -v rsvg-convert >/dev/null; then
	for stage in before after; do
		rsvg-convert -z 2 -b white -o "$out/$stage.png" "$out/$stage.svg"
		[ -f "$out/${stage}_show.svg" ] &&
			rsvg-convert -z 1.5 -b white -o "$out/${stage}_show.png" "$out/${stage}_show.svg"
	done
fi

echo
echo "wrote:"
for f in "$out"/before.* "$out"/after.* "$out"/before_show.* "$out"/after_show.*; do
	[ -f "$f" ] && echo "  $f"
done
