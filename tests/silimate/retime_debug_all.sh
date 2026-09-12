#!/usr/bin/env bash
#
# Throwaway debug helper: run retime_debug.sh over every move opt_retime
# supports today, plus a set of designs it refuses, and collect the renderings
# into one page.
#
# Same side-loading rules as retime_debug.sh: *.sh is not a test target here,
# the designs are read without being touched, and output goes only to /tmp.
#
# usage: ./retime_debug_all.sh
#
# env:
#   YOSYS  yosys binary       (default ../../build/yosys, passed through)
#   OUT    output directory   (default /tmp/retime_debug_all)
#
# Opens with: open /tmp/retime_debug_all/index.html

set -euo pipefail

cd "$(dirname "$0")"

root=${OUT:-/tmp/retime_debug_all}

# design | top | opt_retime args | optional yosys commands to run first
#
# Only moves the pass accepts belong here; the refusals list below has the
# rest, including opt_retime_acc.v, whose accumulator loop still has no legal
# move. Move an entry up here as the pass learns it.
#
# retime_debug_designs.v holds no committed designs, just copies of the modules
# the .ys tests keep as inline heredocs, so those moves show up here too.
#
# Each move gets two renderings. netlistsvg draws a register as the same box at
# any width, so a resize is invisible there and only the register bits column
# gives it away; the graphviz view below it labels every bus, so that is where
# to look for a width change.
#
# Folded values are invisible in both, an init being a wire attribute and a
# reset value a cell parameter, so the "Folded ..." lines printed above each
# pair are the only place they appear. The exception is finerst: a single-bit
# cell spells the value it resets to into its type name, so that fold shows up
# as a changed box label. Enables do draw, as an EN port that survives on the
# moved register and leaves with the ones merged into it.
moves=(
	"opt_retime_buf.v|retime_probe|-flop f1 -cut b2 -forward"
	"opt_retime_buf.v|retime_probe|-flop f1 -cut b3 -forward"
	"opt_retime_add.v|retime_add|-flop fa -cut a0 -forward"
	"opt_retime_add.v|retime_add|-flop fb -cut a0 -forward"
	"opt_retime_add.v|retime_add|-flop fa -cut b0 -forward"
	"opt_retime_add.v|retime_add|-flop fa -cut a1 -forward"
	"opt_retime_mux.v|retime_mux|-flop fa -cut m0 -forward"
	"opt_retime_mux.v|retime_mux|-flop fs -cut m0 -forward"
	"opt_retime_mux.v|retime_mux|-flop fa -cut b0 -forward"
	"opt_retime_cmp.v|retime_cmp|-flop fc -cut r_or -forward"
	"opt_retime_cmp.v|retime_cmp|-flop fa -cut c_eq -forward"
	"opt_retime_cmp.v|retime_cmp|-flop fc -cut r_or -forward + -flop fa -cut g0 -forward"
	"retime_debug_designs.v|carryout|-flop fa -cut a0 -forward"
	"retime_debug_designs.v|narrow|-flop fa -cut a0 -forward"
	"retime_debug_designs.v|bitwise|-flop fa -cut o0 -forward"
	"retime_debug_designs.v|bitwise|-flop fc -cut x0 -forward"
	"retime_debug_designs.v|notpath|-flop fa -cut n0 -forward"
	"retime_debug_designs.v|zeroinit|-flop fa -cut c_ne -forward + -flop fc -cut c_lt -forward + -flop fi -cut c_gt -forward + -flop fe -cut r_and -forward + -flop fg -cut r_xor -forward + -flop fh -cut r_bool -forward"
	"opt_retime_shift.v|retime_shift|-flop famt -cut s_var -forward"
	"opt_retime_shift.v|retime_shift|-flop fd -cut s_const -forward"
	"opt_retime_shift.v|retime_shift|-flop fd -cut s_var -forward"
	"retime_debug_designs.v|onesinit|-flop fa -cut c_xnor -forward + -flop fc -cut r_xnor -forward + -flop fd -cut c_le -forward + -flop fg -cut c_ge -forward"
	"retime_debug_designs.v|enops|-flop fa -cut a0 -forward + -flop fc -cut m0 -forward"
	"retime_debug_designs.v|initmerge|-flop fbuf -cut b1 -forward + -flop fa -cut a0 -forward + -flop fc -cut mm -forward"
	"retime_debug_designs.v|initresize|-flop fr -cut r0 -forward + -flop fca -cut c0 -forward"
	"retime_debug_designs.v|rstfold|-flop fn -cut n0 -forward + -flop fa -cut a0 -forward"
	"retime_debug_designs.v|finerst|-flop ff -cut n0 -forward"
	"retime_debug_designs.v|arstfold|-flop fa -cut o0 -forward"
	"retime_debug_designs.v|tapped|-flop fa -cut a0 -forward"
)

# Designs the pass refuses, in the same format. These get one picture rather
# than a pair, a refused move having produced no after netlist, and they run
# under REFUSE=1 so an entry whose move starts succeeding fails the run instead
# of sitting in the page as a stale claim.
#
# Each is a different reason, and retime_debug_designs.v explains what each one
# shows. Every entry is pinned by a .ys test except the two sliced ones, which
# are a move that ought to work rather than one that should not. sliced appears
# twice because its two entry points fail two independent checks: from the wide
# operand there is no single driver for input A, and from a slice the chain walk
# never reaches the cut.
refusals=(
	"retime_debug_designs.v|unflopped|-flop fa -cut a0 -forward"
	"retime_debug_designs.v|halfconst|-flop fa -cut a0 -forward"
	"retime_debug_designs.v|liveselect|-flop fa -cut m0 -forward"
	"retime_debug_designs.v|enmix|-flop fa -cut a0 -forward"
	"retime_debug_designs.v|rstmix|-flop fa -cut a0 -forward"
	"retime_debug_designs.v|mixinit|-flop fa -cut a0 -forward"
	"retime_debug_designs.v|signedshift|-flop fa -cut s0 -forward"
	"retime_debug_designs.v|fine|-flop fa -cut a0 -forward"
	"retime_debug_designs.v|sliced|-flop fb -cut a0 -forward"
	"retime_debug_designs.v|sliced|-flop f0 -cut a0 -forward"
	"opt_retime_acc.v|retime_acc|-flop f_acc -cut a_acc -forward"
)

rm -rf "$root"
mkdir -p "$root"

# Spelling out every move stops being readable past a couple of them.
# grep -c exits 1 on a zero count, which set -e would treat as fatal.
label_for() {
	local nmoves
	nmoves=$(( $(echo "$2" | tr ' ' '\n' | grep -c '^+$' || true) + 1 ))
	if [ "$nmoves" -gt 2 ]; then
		echo "$1_${nmoves}_moves"
	else
		echo "$1 $2" | sed 's/-flop //g; s/-cut //g; s/ + /_then_/g; s/-//g; s/ /_/g'
	fi
}

for entry in "${moves[@]}"; do
	IFS='|' read -r design top move pre <<<"$entry"
	label=$(label_for "$top" "$move")
	echo "=== $top: $move"
	OUT="$root/$label" PRE="${pre:-}" ./retime_debug.sh "$design" "$top" $move >"$root/$label.log" 2>&1
	grep -E '^(Retimed|Resizing|Folded|Leaving|Kept) ' "$root/$label.log" | sed 's/^/  /' || true
done

for entry in "${refusals[@]}"; do
	IFS='|' read -r design top move pre <<<"$entry"
	# Prefixed so the two groups stay apart in the output directory; the page
	# itself keys off the refusal.txt that REFUSE=1 leaves behind.
	label=refused_$(label_for "$top" "$move")
	echo "=== $top (refused): $move"
	if ! OUT="$root/$label" PRE="${pre:-}" REFUSE=1 \
			./retime_debug.sh "$design" "$top" $move >"$root/$label.log" 2>&1; then
		echo "  entry failed, see $root/$label.log" >&2
		exit 1
	fi
	grep -E '^refused: ' "$root/$label.log" | sed 's/^/  /' || true
done

# One page with every before/after pair, plus how many registers each move
# cost or saved.
python3 - "$root" <<'PY'
import json, os, sys

root = sys.argv[1]
# Prefixes, so the enable and reset variants come along: $dffe and $dffsr with
# $dff, $sdffe with $sdff, and every single-bit flop with $_DFF or $_SDFF. The
# fine reset cells are the ones that matter here, since $_SDFF_PP0_ matches
# none of the coarse names and would otherwise be counted as combinational.
FF = ("$dff", "$sdff", "$adff", "$aldff", "$_DFF", "$_SDFF", "$_ALDFF")


def regs(path):
    with open(path) as f:
        design = json.load(f)
    cells = [c for m in design["modules"].values() for c in m["cells"].values()]
    ffs = [c for c in cells if c["type"].startswith(FF)]
    return len(ffs), sum(len(c["connections"]["Q"]) for c in ffs)


def esc(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


rows = []
refused = []
for label in sorted(os.listdir(root)):
    d = os.path.join(root, label)
    if not os.path.isdir(d):
        continue
    # REFUSE=1 leaves a refusal.txt and no after netlist, which is what tells
    # the two kinds of entry apart here.
    reason_path = os.path.join(d, "refusal.txt")
    if os.path.exists(reason_path):
        with open(reason_path) as f:
            refused.append((label, f.read().strip(), regs(os.path.join(d, "before.json"))))
        continue
    before, after = regs(os.path.join(d, "before.json")), regs(os.path.join(d, "after.json"))
    note = ""
    with open(d + ".log") as f:
        for line in f:
            if line.startswith(("Retimed", "Resizing", "Folded", "Leaving", "Kept")):
                note += line.strip() + " "
    rows.append((label, before, after, note))

html = ["<html><head><style>",
        "body{font:14px -apple-system,sans-serif;margin:2em;max-width:1400px}",
        "h2{margin-top:2.5em;border-top:1px solid #ccc;padding-top:1em}",
        "td{vertical-align:top;padding:4px 12px}img{max-width:640px;border:1px solid #eee}",
        "th.sub{padding-top:1.5em;font-weight:normal;color:#666}",
        "code{background:#f4f4f4;padding:1px 4px}",
        "</style></head><body>",
        "<h1>opt_retime before / after</h1>",
        "<table><tr><th align=left>move</th><th align=left>registers</th>"
        "<th align=left>register bits</th></tr>"]
for label, before, after, _ in rows:
    html.append("<tr><td><code>%s</code></td><td>%d &rarr; %d</td><td>%d &rarr; %d</td></tr>"
                % (label, before[0], after[0], before[1], after[1]))
html.append("</table>")

for label, before, after, note in rows:
    html.append("<h2>%s</h2>" % label)
    html.append("<p>%s registers %d &rarr; %d, register bits %d &rarr; %d</p>"
                % (note, before[0], after[0], before[1], after[1]))
    html.append("<table><tr><th align=left>before</th><th align=left>after</th></tr>"
                "<tr><td><img src='%s/before.svg'></td>"
                "<td><img src='%s/after.svg'></td></tr>" % (label, label))
    # The graphviz pair is absent when dot is not installed.
    if os.path.exists(os.path.join(root, label, "before_show.svg")):
        html.append("<tr><th align=left colspan=2 class=sub>with bus widths and port names</th></tr>"
                    "<tr><td><img src='%s/before_show.svg'></td>"
                    "<td><img src='%s/after_show.svg'></td></tr>" % (label, label))
    html.append("</table>")

if refused:
    html.append("<h1 style='margin-top:3em;border-top:3px solid #999;padding-top:1em'>"
                "refused moves</h1>")
    html.append("<p>One picture each rather than a pair, since a refused move leaves no "
                "after netlist to draw. These run under <code>REFUSE=1</code>, so a move "
                "the pass learns breaks this page instead of leaving a stale claim in it. "
                "<code>retime_debug_designs.v</code> says what each one is showing; the "
                "reasons below are verbatim from the pass.</p>")
    html.append("<table><tr><th align=left>move</th><th align=left>registers</th>"
                "<th align=left>reason</th></tr>")
    for label, reason, before in refused:
        html.append("<tr><td><code>%s</code></td><td>%d (%d bits)</td><td>%s</td></tr>"
                    % (label, before[0], before[1], esc(reason)))
    html.append("</table>")
    for label, reason, before in refused:
        html.append("<h2>%s</h2>" % label)
        html.append("<p>%s<br>%d registers, %d register bits</p>"
                    % (esc(reason), before[0], before[1]))
        html.append("<table><tr><th align=left>netlist as the pass saw it</th></tr>"
                    "<tr><td><img src='%s/before.svg'></td></tr>" % label)
        if os.path.exists(os.path.join(root, label, "before_show.svg")):
            html.append("<tr><th align=left class=sub>with bus widths and port names</th></tr>"
                        "<tr><td><img src='%s/before_show.svg'></td></tr>" % label)
        html.append("</table>")

html.append("</body></html>")

with open(os.path.join(root, "index.html"), "w") as f:
    f.write("\n".join(html))

print()
print("%-40s %-12s %s" % ("move", "registers", "register bits"))
for label, before, after, _ in rows:
    print("%-40s %-12s %s" % (label, "%d -> %d" % (before[0], after[0]),
                              "%d -> %d" % (before[1], after[1])))
if refused:
    print()
    print("%-40s %s" % ("refused", "reason"))
    for label, reason, _ in refused:
        print("%-40s %s" % (label, reason))
print()
print("open %s/index.html" % root)
PY
