#!/usr/bin/env bash
#
# Throwaway debug helper: run retime_debug.sh over every move opt_retime
# supports today and collect the renderings into one page.
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

# design | top | opt_retime args
#
# Only moves the pass accepts belong here. opt_retime_shift.v and _acc.v have
# no legal move yet (the shifts and the accumulator loop are both still
# refused), so they are absent on purpose. Add them as the pass learns them.
#
# retime_debug_designs.v holds no committed designs, just copies of the modules
# the .ys tests keep as inline heredocs, so those moves show up here too.
#
# Each move gets two renderings. netlistsvg draws a register as the same box at
# any width, so a resize is invisible there and only the register bits column
# gives it away; the graphviz view below it labels every bus, so that is where
# to look for a width change.
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
	"retime_debug_designs.v|siblings|-flop fa -cut c_ne -forward + -flop fc -cut c_lt -forward + -flop fe -cut r_and -forward + -flop fg -cut r_xor -forward + -flop fh -cut r_bool -forward"
	"retime_debug_designs.v|inverting|-flop fa -cut c_xnor -forward + -flop fc -cut r_xnor -forward"
)

rm -rf "$root"
mkdir -p "$root"

for entry in "${moves[@]}"; do
	IFS='|' read -r design top move <<<"$entry"
	# Spelling out every move stops being readable past a couple of them.
	# grep -c exits 1 on a zero count, which set -e would treat as fatal
	nmoves=$(( $(echo "$move" | tr ' ' '\n' | grep -c '^+$' || true) + 1 ))
	if [ "$nmoves" -gt 2 ]; then
		label="${top}_${nmoves}_moves"
	else
		label=$(echo "$top $move" | sed 's/-flop //g; s/-cut //g; s/ + /_then_/g; s/-//g; s/ /_/g')
	fi
	echo "=== $top: $move"
	OUT="$root/$label" ./retime_debug.sh "$design" "$top" $move >"$root/$label.log" 2>&1
	grep -E '^(Retimed|Resizing) ' "$root/$label.log" | sed 's/^/  /' || true
done

# One page with every before/after pair, plus how many registers each move
# cost or saved.
python3 - "$root" <<'PY'
import json, os, sys

root = sys.argv[1]
FF = ("$dff", "$sdff", "$adff", "$_DFF_P_", "$_DFF_N_")


def regs(path):
    with open(path) as f:
        design = json.load(f)
    cells = [c for m in design["modules"].values() for c in m["cells"].values()]
    ffs = [c for c in cells if c["type"].startswith(FF)]
    return len(ffs), sum(len(c["connections"]["Q"]) for c in ffs)


rows = []
for label in sorted(os.listdir(root)):
    d = os.path.join(root, label)
    if not os.path.isdir(d):
        continue
    before, after = regs(os.path.join(d, "before.json")), regs(os.path.join(d, "after.json"))
    note = ""
    with open(d + ".log") as f:
        for line in f:
            if line.startswith(("Retimed", "Resizing")):
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
html.append("</body></html>")

with open(os.path.join(root, "index.html"), "w") as f:
    f.write("\n".join(html))

print()
print("%-40s %-12s %s" % ("move", "registers", "register bits"))
for label, before, after, _ in rows:
    print("%-40s %-12s %s" % (label, "%d -> %d" % (before[0], after[0]),
                              "%d -> %d" % (before[1], after[1])))
print()
print("open %s/index.html" % root)
PY
