#!/usr/bin/env bash
#
# Throwaway debug helper: run retime_debug_diff.sh over every move opt_retime
# supports today, plus a set of designs it refuses, and collect the
# neighborhood renderings into one page.
#
# Same side-loading rules as retime_debug.sh: *.sh is not a test target here,
# the designs are read without being touched, and output goes only to /tmp.
# Same move list as retime_debug_all.sh, so the two galleries stay in lockstep.
#
# usage: ./retime_debug_diff_all.sh
#
# env:
#   YOSYS  yosys binary       (default ../../build/yosys, passed through)
#   OUT    output directory   (default /tmp/retime_debug_diff_all)
#   HOPS, CONE, CLEAN, NETLISTSVG, NETLISTSVG_DIR
#          passed through to retime_debug_diff.sh
#
# Opens with: open /tmp/retime_debug_diff_all/index.html

set -euo pipefail

cd "$(dirname "$0")"

root=${OUT:-/tmp/retime_debug_diff_all}

# design | top | opt_retime args | optional yosys commands to run first
#
# Keep this list identical to retime_debug_all.sh.
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

# Designs the pass refuses. Keep this list identical to retime_debug_all.sh
# too. A refused move has no diff to seed a neighborhood from, so these are
# seeded from the cells the move named instead, the flop and the cut, and only
# the before side is drawn. This is the gallery to read for retime_acc, whose
# full netlist is too big to take in at once.
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
	OUT="$root/$label" PRE="${pre:-}" ./retime_debug_diff.sh "$design" "$top" $move >"$root/$label.log" 2>&1
	grep -E '^(Retimed|Resizing|Folded|seeds:|  moved:|  collateral:|  added:) ' "$root/$label.log" | sed 's/^/  /' || true
done

for entry in "${refusals[@]}"; do
	IFS='|' read -r design top move pre <<<"$entry"
	label=refused_$(label_for "$top" "$move")
	echo "=== $top (refused): $move"
	if ! OUT="$root/$label" PRE="${pre:-}" REFUSE=1 \
			./retime_debug_diff.sh "$design" "$top" $move >"$root/$label.log" 2>&1; then
		echo "  entry failed, see $root/$label.log" >&2
		exit 1
	fi
	grep -E '^(refused:|seeds:) ' "$root/$label.log" | sed 's/^/  /' || true
done

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


def seeds(path):
    info = {"moved": "", "collateral": "", "added_cells": "", "added_wires": "",
            "deleted_cells": "", "changed_cells": ""}
    if not os.path.exists(path):
        return info
    with open(path) as f:
        for line in f:
            key, _, val = line.partition(":")
            if key in info:
                info[key] = val.strip()
    return info


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
        full_b = os.path.join(d, "before_full.json")
        if not os.path.exists(full_b):
            full_b = os.path.join(d, "before.json")
        with open(reason_path) as f:
            refused.append((label, f.read().strip(), regs(full_b),
                            seeds(os.path.join(d, "seeds.txt"))))
        continue
    full_b = os.path.join(d, "before_full.json")
    full_a = os.path.join(d, "after_full.json")
    if not os.path.exists(full_b):
        full_b = os.path.join(d, "before.json")
        full_a = os.path.join(d, "after.json")
    before, after = regs(full_b), regs(full_a)
    note = ""
    with open(d + ".log") as f:
        for line in f:
            if line.startswith(("Retimed", "Resizing", "Folded")):
                note += line.strip() + " "
    rows.append((label, before, after, note, seeds(os.path.join(d, "seeds.txt"))))

html = ["<html><head><style>",
        "body{font:14px -apple-system,sans-serif;margin:2em;max-width:1400px}",
        "h2{margin-top:2.5em;border-top:1px solid #ccc;padding-top:1em}",
        "td{vertical-align:top;padding:4px 12px}img{max-width:640px;border:1px solid #eee}",
        "th.sub{padding-top:1.5em;font-weight:normal;color:#666}",
        "code{background:#f4f4f4;padding:1px 4px}",
        "</style></head><body>",
        "<h1>opt_retime before / after (diff neighborhood)</h1>",
        "<p>Each pair is the RTLIL-diff seed plus a combinational hop around it. "
        "<span style='color:#c62828'>Red</span> is the flop being moved (before), "
        "<span style='color:#2e7d32'>green</span> is that same flop after it hops, "
        "<span style='color:#ef6c00'>orange</span> is a sibling flop the merge deleted.</p>",
        "<table><tr><th align=left>move</th><th align=left>registers</th>"
        "<th align=left>register bits</th><th align=left>moved</th>"
        "<th align=left>collateral</th></tr>"]
for label, before, after, _, info in rows:
    html.append("<tr><td><code>%s</code></td><td>%d &rarr; %d</td><td>%d &rarr; %d</td>"
                "<td>%s</td><td>%s</td></tr>"
                % (label, before[0], after[0], before[1], after[1],
                   info["moved"] or "&mdash;", info["collateral"] or "&mdash;"))
html.append("</table>")

for label, before, after, note, info in rows:
    html.append("<h2>%s</h2>" % label)
    html.append("<p>%s registers %d &rarr; %d, register bits %d &rarr; %d</p>"
                % (note, before[0], after[0], before[1], after[1]))
    html.append("<p>moved <code>%s</code><br>collateral <code>%s</code><br>added <code>%s</code></p>"
                % (info["moved"] or "(none)",
                   info["collateral"] or "(none)",
                   " ".join(x for x in (info["added_cells"], info["added_wires"]) if x) or "(none)"))
    html.append("<table><tr><th align=left>before</th><th align=left>after</th></tr>"
                "<tr><td><img src='%s/before.svg'></td>"
                "<td><img src='%s/after.svg'></td></tr>" % (label, label))
    if os.path.exists(os.path.join(root, label, "before_show.svg")):
        html.append("<tr><th align=left colspan=2 class=sub>with bus widths and port names</th></tr>"
                    "<tr><td><img src='%s/before_show.svg'></td>"
                    "<td><img src='%s/after_show.svg'></td></tr>" % (label, label))
    html.append("</table>")

if refused:
    html.append("<h1 style='margin-top:3em;border-top:3px solid #999;padding-top:1em'>"
                "refused moves</h1>")
    html.append("<p>One picture each rather than a pair, since a refused move leaves no "
                "after netlist to draw, and with it no diff to seed a neighborhood from: "
                "these are seeded from the cells the move named instead, so "
                "<span style='color:#c62828'>red</span> is the flop that could not move "
                "and the cut it could not reach is in the same view. These run under "
                "<code>REFUSE=1</code>, so a move the pass learns breaks this page "
                "instead of leaving a stale claim in it. "
                "<code>retime_debug_designs.v</code> says what each one is showing; the "
                "reasons below are verbatim from the pass.</p>")
    html.append("<table><tr><th align=left>move</th><th align=left>registers</th>"
                "<th align=left>reason</th></tr>")
    for label, reason, before, _ in refused:
        html.append("<tr><td><code>%s</code></td><td>%d (%d bits)</td><td>%s</td></tr>"
                    % (label, before[0], before[1], esc(reason)))
    html.append("</table>")
    for label, reason, before, info in refused:
        html.append("<h2>%s</h2>" % label)
        html.append("<p>%s<br>%d registers, %d register bits</p>"
                    % (esc(reason), before[0], before[1]))
        html.append("<p>could not move <code>%s</code></p>" % (info["moved"] or "(none)"))
        # Whole module, unlike the accepted entries: a refused move has no diff
        # to build a neighborhood around, so the register count above and the
        # picture below agree.
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
print("%-40s %-12s %-16s %s" % ("move", "registers", "register bits", "collateral"))
for label, before, after, _, info in rows:
    print("%-40s %-12s %-16s %s" % (label, "%d -> %d" % (before[0], after[0]),
                                    "%d -> %d" % (before[1], after[1]),
                                    info["collateral"] or "-"))
if refused:
    print()
    print("%-40s %s" % ("refused", "reason"))
    for label, reason, _, _ in refused:
        print("%-40s %s" % (label, reason))
print()
print("open %s/index.html" % root)
PY
