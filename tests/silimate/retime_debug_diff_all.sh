#!/usr/bin/env bash
#
# Throwaway debug helper: run retime_debug_diff.sh over every move opt_retime
# supports today and collect the neighborhood renderings into one page.
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
	"opt_retime_shift.v|retime_shift|-flop famt -cut s_var -forward|splitfanout"
	"opt_retime_shift.v|retime_shift|-flop fd -cut s_const -forward|splitfanout"
	"retime_debug_designs.v|onesinit|-flop fa -cut c_xnor -forward + -flop fc -cut r_xnor -forward + -flop fd -cut c_le -forward + -flop fg -cut c_ge -forward"
	"retime_debug_designs.v|enops|-flop fa -cut a0 -forward + -flop fc -cut m0 -forward"
	"retime_debug_designs.v|initmerge|-flop fbuf -cut b1 -forward + -flop fa -cut a0 -forward + -flop fc -cut mm -forward"
	"retime_debug_designs.v|initresize|-flop fr -cut r0 -forward + -flop fca -cut c0 -forward"
	"retime_debug_designs.v|rstfold|-flop fn -cut n0 -forward + -flop fa -cut a0 -forward"
	"retime_debug_designs.v|finerst|-flop ff -cut n0 -forward"
	"retime_debug_designs.v|arstfold|-flop fa -cut o0 -forward"
)

rm -rf "$root"
mkdir -p "$root"

for entry in "${moves[@]}"; do
	IFS='|' read -r design top move pre <<<"$entry"
	nmoves=$(( $(echo "$move" | tr ' ' '\n' | grep -c '^+$' || true) + 1 ))
	if [ "$nmoves" -gt 2 ]; then
		label="${top}_${nmoves}_moves"
	else
		label=$(echo "$top $move" | sed 's/-flop //g; s/-cut //g; s/ + /_then_/g; s/-//g; s/ /_/g')
	fi
	echo "=== $top: $move"
	OUT="$root/$label" PRE="${pre:-}" ./retime_debug_diff.sh "$design" "$top" $move >"$root/$label.log" 2>&1
	grep -E '^(Retimed|Resizing|Folded|seeds:|  moved:|  collateral:|  added:) ' "$root/$label.log" | sed 's/^/  /' || true
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


rows = []
for label in sorted(os.listdir(root)):
    d = os.path.join(root, label)
    if not os.path.isdir(d):
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
html.append("</body></html>")

with open(os.path.join(root, "index.html"), "w") as f:
    f.write("\n".join(html))

print()
print("%-40s %-12s %-16s %s" % ("move", "registers", "register bits", "collateral"))
for label, before, after, _, info in rows:
    print("%-40s %-12s %-16s %s" % (label, "%d -> %d" % (before[0], after[0]),
                                    "%d -> %d" % (before[1], after[1]),
                                    info["collateral"] or "-"))
print()
print("open %s/index.html" % root)
PY
