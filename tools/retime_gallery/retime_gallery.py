#!/usr/bin/env python3
# ./retime_gallery.py  ->  /tmp/retime_debug_diff_all/index.html

import json
import os
import re
import shutil
import subprocess
import sys
from concurrent.futures import ProcessPoolExecutor, as_completed
from contextlib import redirect_stderr, redirect_stdout
from html import escape
from io import StringIO
from pathlib import Path

HERE = Path(__file__).resolve().parent
DESIGNS = HERE / "designs"
OUT_ROOT = Path("/tmp/retime_debug_diff_all")
NLSVG_DIR = Path("/tmp/retime_debug_netlistsvg")
HOPS = 3
WORKERS = min(32, (os.cpu_count() or 4) * 2)
EMPTY = "n:$__diff_empty__"
FF_TYPES = ("$dff", "$dffe", "$adff", "$sdff", "$adffe", "$sdffe", "$aldff", "$dlatch")
FF_COUNT = ("$dff", "$sdff", "$adff", "$aldff", "$_DFF", "$_SDFF", "$_ALDFF")

# design.v top args   — omit design.v to use retime_debug_designs.v
MOVES = """\
opt_retime_buf.v retime_probe -flop f1 -cut b2 -forward
opt_retime_buf.v retime_probe -flop f1 -cut b3 -forward
opt_retime_buf.v retime_probe -flop f1 -cut b1 -backward
opt_retime_add.v retime_add -flop fa -cut a0 -forward
opt_retime_add.v retime_add -flop fb -cut a0 -forward
opt_retime_add.v retime_add -flop fa -cut b0 -forward
opt_retime_add.v retime_add -flop fa -cut a1 -forward
opt_retime_mux.v retime_mux -flop fa -cut m0 -forward
opt_retime_mux.v retime_mux -flop fs -cut m0 -forward
opt_retime_mux.v retime_mux -flop fa -cut b0 -forward
opt_retime_cmp.v retime_cmp -flop fc -cut r_or -forward
opt_retime_cmp.v retime_cmp -flop fa -cut c_eq -forward
opt_retime_cmp.v retime_cmp -flop fc -cut r_or -forward + -flop fa -cut g0 -forward
opt_retime_cmp.v retime_cmp -flop fq -cut g0 -backward
carryout -flop fa -cut a0 -forward
narrow -flop fa -cut a0 -forward
fullmul -flop fa -cut m0 -forward
divcut -flop fa -cut d0 -forward
pmuxcut -flop fa -cut m0 -forward
signedmul -flop fa -cut m0 -forward
bitwise -flop fa -cut o0 -forward
bitwise -flop fc -cut x0 -forward
notpath -flop fa -cut n0 -forward
zeroinit -flop fa -cut c_ne -forward + -flop fc -cut c_lt -forward + -flop fi -cut c_gt -forward + -flop fe -cut r_and -forward + -flop fg -cut r_xor -forward + -flop fh -cut r_bool -forward
opt_retime_shift.v retime_shift -flop famt -cut s_var -forward
opt_retime_shift.v retime_shift -flop fd -cut s_const -forward
opt_retime_shift.v retime_shift -flop fd -cut s_var -forward
onesinit -flop fa -cut c_xnor -forward + -flop fc -cut r_xnor -forward + -flop fd -cut c_le -forward + -flop fg -cut c_ge -forward
enops -flop fa -cut a0 -forward + -flop fc -cut m0 -forward
initmerge -flop fbuf -cut b1 -forward + -flop fa -cut a0 -forward + -flop fc -cut mm -forward
initresize -flop fr -cut r0 -forward + -flop fca -cut c0 -forward
rstfold -flop fn -cut n0 -forward + -flop fa -cut a0 -forward
finerst -flop ff -cut n0 -forward
arstfold -flop fa -cut o0 -forward
tapped -flop fa -cut a0 -forward
halfconst -flop fa -cut a0 -forward
sliced -flop fb -cut a0 -forward
sliced -flop f0 -cut a0 -forward
signedshift -flop fa -cut s0 -forward
signedleft -flop fa -cut s0 -forward
constops -flop fa -cut a_inc -forward + -flop fb -cut a_mask -forward
subdes -flop fa -cut s0 -forward
aldffeq -flop fs -cut e0 -forward
addc -flop f -cut a0 -backward
invcap -flop f -cut n0 -backward
andc -flop f -cut a0 -backward
andlive -flop f -cut a0 -backward
mulc -flop f -cut m0 -backward
muleven -flop f -cut m0 -backward
mullive -flop f -cut m0 -backward
muxa -flop f -cut u0 -backward
muxb -flop f -cut u0 -backward
muxrst -flop f -cut u0 -backward
unflopped -flop fq -cut a0 -backward
muxtree -flop f -cut u2 -backward
muxtree -flop f -cut u0 -backward
backfanout -flop fq -cut b0 -backward
sharedcone -flop f1 -cut a0 -backward
sharedcone -flop f1 -cut a0 -backward + -flop f2 -cut a0_dup -backward
shareddeep -flop fq -cut a0 -backward
fanout2 -flop f1 -cut a0 -backward -all-fanouts
fanout3 -flop f1 -cut a0 -backward -all-fanouts
fanoutdeep -flop f1 -cut a0 -backward -all-fanouts
gated -flop f1 -cut a0 -backward
gatedin -flop f1 -cut a0 -backward
gatedfwd -flop fa -cut a0 -forward
midcut -flop fa -cut n2 -forward
midtap -flop fa -cut n1 -forward
""".splitlines()

REFUSALS = """\
unflopped -flop fa -cut a0 -forward
liveselect -flop fa -cut m0 -forward
enmix -flop fa -cut a0 -forward
rstmix -flop fa -cut a0 -forward
mixinit -flop fa -cut a0 -forward
fine -flop fa -cut a0 -forward
opt_retime_acc.v retime_acc -flop f_acc -cut a_acc -forward
opt_retime_buf.v retime_probe -flop f1 -cut b0 -backward
signedshift -flop fq -cut s0 -backward
backwide -flop fq -cut a0 -backward
selpath -flop f -cut u0 -backward
andmask -flop f -cut a0 -backward
mulevenodd -flop f -cut m0 -backward
allconst -flop f -cut a0 -backward
gatecut -flop fa -cut g0 -forward
aloadnet -flop fa -cut n0 -forward
sharedrecon -flop fq -cut a0 -backward
sharedouttap -flop f1 -cut a0 -backward
fanoutsr -flop f1 -cut a0 -backward -all-fanouts
fanouten -flop f1 -cut a0 -backward -all-fanouts
twogates -flop fa -cut a0 -forward
midtap -flop fa -cut n2 -forward
""".splitlines()


def parse_row(line):
    toks = line.split()
    if toks[0].endswith(".v"):
        return toks[0], toks[1], " ".join(toks[2:])
    return "retime_debug_designs.v", toks[0], " ".join(toks[1:])


def label_for(top, args):
    n = args.split().count("+") + 1
    if n > 2:
        return f"{top}_{n}_moves"
    t = f"{top} {args}".replace("-flop ", "").replace("-cut ", "").replace(" + ", "_then_").replace("-", "")
    return "_".join(t.split())


def yosys_bin():
    path = shutil.which("yosys")
    if not path:
        sys.exit("yosys not on PATH")
    return path


def sh(cmd, check=False):
    r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=check)
    return r.returncode, r.stdout or ""


def yosys_p(yosys, script, quiet=False):
    cmd = [str(yosys)] + (["-q"] if quiet else []) + ["-p", script]
    rc, text = sh(cmd)
    if quiet and rc:
        raise RuntimeError(text or "yosys failed")
    return rc, text


def parse_move(args):
    cmds, cur, flops, cuts, prev = [], [], [], [], ""
    for tok in args.split() + ["+"]:
        if tok == "+":
            cmds.append("opt_retime " + " ".join(cur) + ";")
            cur = []
        else:
            cur.append(tok)
        if prev == "-flop":
            flops.append(tok)
        if prev == "-cut":
            cuts.append(tok)
        prev = tok
    return " ".join(cmds), flops, cuts


def first_line(text, prefix):
    return next((ln[len(prefix) :].strip() for ln in text.splitlines() if ln.startswith(prefix)), "")


def refusal_reason(log_text, scratch):
    if scratch.exists():
        lines = [
            ln.strip()
            for ln in scratch.read_text().splitlines()
            if ln.strip() and not ln.startswith("Executing ") and "not set" not in ln
        ]
        if lines:
            return " ".join(lines)
    return first_line(log_text, "Refused:") or first_line(log_text, "ERROR:")


def unesc(name):
    return name.removeprefix("\\")


def is_ff(cell_text):
    typ = unesc(cell_text.split()[1])
    return typ in FF_TYPES or typ.startswith(("$_DFF", "$_SDFF", "$_DLATCH"))


def parse_rtlil(path):
    cells, wires, assigns, in_mod, in_cell, cname, clines = {}, {}, {}, False, False, None, []
    for line in path.read_text().splitlines():
        s = line.strip()
        if not in_mod:
            in_mod = s.startswith("module ")
            continue
        if in_cell:
            if s.startswith(("parameter ", "connect ")):
                clines.append(s)
            elif s == "end":
                cells[cname] = "\n".join(clines)
                in_cell = False
            continue
        if s == "end":
            in_mod = False
        elif s.startswith("cell "):
            cname, clines, in_cell = unesc(s.split()[-1]), [s], True
        elif s.startswith("wire "):
            wires[unesc(s.split()[-1])] = s
        elif s.startswith("connect "):
            assigns[unesc(s.split()[1])] = s
    return cells, wires, assigns


def classify(a, b):
    return (sorted(set(b) - set(a)), sorted(set(a) - set(b)), sorted(n for n in set(a) & set(b) if a[n] != b[n]))


def sel(cells, wires=()):
    return " ".join([f"c:{n}" for n in cells] + [f"w:{n}" for n in wires]) or EMPTY


def load_sel(path):
    return [ln.strip() for ln in path.read_text().splitlines() if ln.strip()] if path.exists() else []


def write_seeds(out, refuse, cuts, flops):
    ba, wa, aa = parse_rtlil(out / "before.il")
    moved = list(dict.fromkeys(flops))
    if refuse:
        moved = [n for n in moved if n in ba]
        seed_c, seed_w = sorted(set(moved) | {c for c in cuts if c in ba}), []
        add_c = del_c = ch_c = add_w = del_w = collateral = []
    else:
        bb, wb, ab = parse_rtlil(out / "after.il")
        add_c, del_c, ch_c = classify(ba, bb)
        add_w, del_w, ch_w = classify({**wa, **aa}, {**wb, **ab})
        seed_c = sorted(set(add_c) | set(del_c) | set(ch_c))
        seed_w = sorted(set(add_w) | set(del_w) | set(ch_w))
        moved = [n for n in moved if n in ba or n in bb]
        collateral = [n for n in del_c if n not in moved and is_ff(ba[n])]
    (out / "seeds.txt").write_text(
        f"cells: {' '.join(seed_c)}\nwires: {' '.join(seed_w)}\nmoved: {' '.join(moved)}\n"
        f"collateral: {' '.join(collateral)}\nadded_cells: {' '.join(add_c)}\ndeleted_cells: {' '.join(del_c)}\n"
        f"changed_cells: {' '.join(ch_c)}\nadded_wires: {' '.join(add_w)}\ndeleted_wires: {' '.join(del_w)}\n"
    )
    (out / "diff_colors.json").write_text(
        json.dumps({"moved": moved, "collateral": collateral, "added": add_c + add_w})
    )
    if not seed_c and not seed_w:
        (out / "seeds.ys").write_text("")
        print("seeds: none (" + ("no cells named" if refuse else "no structural RTLIL diff") + ")")
        return False
    view = "select -set view *" if refuse else f"select -set view @seed %cie{HOPS} @seed %coe{HOPS} %u"
    (out / "seeds.ys").write_text(
        f"select -set seed {sel(seed_c, seed_w)}\nselect -set moved {sel(moved)}\n"
        f"select -set collateral {sel(collateral)}\nselect -set added {sel(add_c, add_w)}\n{view}\n"
    )
    print(f"seeds: {len(seed_c)} cell(s), {len(seed_w)} wire(s)")
    print(f"  moved:       {' '.join(moved) or '(none)'}")
    print(f"  collateral:  {' '.join(collateral) or '(none)'}")
    print(f"  added:       {' '.join(add_c + add_w) or '(none)'}")
    return True


def colorize_svg(svg_path, stage, colors):
    def ident(name):
        return "cell_" + re.sub(r"([^A-Za-z0-9_-])", lambda m: f"\\{ord(m.group(1)):x} ", name)

    def rules(names, stroke, fill):
        out = []
        for n in names:
            i = ident(n)
            out += [
                f"rect.{i}, path.{i}, circle.{i} {{ stroke: {stroke}; fill: {fill}; }}",
                f"line.{i} {{ stroke: {stroke}; }}",
            ]
        return out

    css = (
        rules(colors.get("moved") or [], "#c62828", "#ffcdd2")
        + rules(colors.get("collateral") or [], "#ef6c00", "#ffe0b2")
        if stage == "before"
        else rules(colors.get("moved") or [], "#2e7d32", "#c8e6c9")
        + rules(colors.get("added") or [], "#2e7d32", "#c8e6c9")
    )
    text = svg_path.read_text()
    gt = text.find(">")
    if css and gt >= 0:
        svg_path.write_text(text[: gt + 1] + "\n<style>\n" + "\n".join(css) + "\n</style>\n" + text[gt + 1 :])


def netlistsvg():
    bin_ = NLSVG_DIR / "node_modules" / ".bin" / "netlistsvg"
    if not (bin_.exists() and os.access(bin_, os.X_OK)):
        print(f"installing netlistsvg into {NLSVG_DIR} (one time)")
        NLSVG_DIR.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            ["npm", "install", "--silent", "--prefix", str(NLSVG_DIR), "netlistsvg"],
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
    return bin_


def rasterize(path, zoom):
    if shutil.which("rsvg-convert") and path.exists():
        subprocess.run(
            ["rsvg-convert", "-z", str(zoom), "-b", "white", "-o", str(path.with_suffix(".png")), str(path)],
            check=False,
        )


def yosys_on(yosys, out, top, stage, extra):
    yosys_p(yosys, f"read_rtlil {out / f'{stage}.il'}\ncd {top}\n{extra}", quiet=True)


def expand_view(yosys, out, top):
    def dump_sel(stage, ys):
        yosys_on(yosys, out, top, stage, ys.read_text().rstrip() + f"\nselect -write {out / f'{stage}_view.sel'} @view")

    def dump_json(stage, ys, dest):
        yosys_on(
            yosys,
            out,
            top,
            stage,
            ys.read_text().rstrip()
            + f"\nsubmod -copy -noclean -name diffview @view\nselect -clear\nselect diffview\nwrite_json -selected {dest}",
        )

    dump_sel("before", out / "seeds.ys")
    dump_sel("after", out / "seeds.ys")
    before, after = load_sel(out / "before_view.sel"), load_sel(out / "after_view.sel")
    union = sorted(set(before) | set(after))
    (out / "view_union.sel").write_text("\n".join(union) + ("\n" if union else ""))
    print(f"view: {len(union)} object(s) (union of {len(before)} before, {len(after)} after)")
    (out / "seeds_union.ys").write_text(
        (out / "seeds.ys").read_text().rstrip() + f"\nselect -set view -read {out / 'view_union.sel'}\n"
    )
    dump_json("before", out / "seeds_union.ys", out / "before_view.json")
    dump_json("after", out / "seeds_union.ys", out / "after_view.json")

    def ports(p):
        return set(next(iter(json.loads(p.read_text())["modules"].values())).get("ports", {}))

    bp, ap = ports(out / "before_view.json"), ports(out / "after_view.json")
    xor = sorted(bp ^ ap)
    (out / "xor_ports.sel").write_text("".join(f"{top}/{n}\n" for n in xor))
    if xor:
        print(
            f"view: unmatched ports {' '.join(sorted(bp - ap)) or '(none)'} vs {' '.join(sorted(ap - bp)) or '(none)'}"
        )
        (out / "seeds_expand.ys").write_text(
            (out / "seeds_union.ys").read_text().rstrip()
            + f"\nselect -set xorw -read {out / 'xor_ports.sel'}\nselect -set view @view @xorw %x1:-[CLK,C,EN] %u\n"
        )
        yosys_on(
            yosys,
            out,
            top,
            "before",
            (out / "seeds_expand.ys").read_text().rstrip() + f"\nselect -write {out / 'before_viewx.sel'} @view",
        )
        yosys_on(
            yosys,
            out,
            top,
            "after",
            (out / "seeds_expand.ys").read_text().rstrip() + f"\nselect -write {out / 'after_viewx.sel'} @view",
        )
        union = sorted(set(load_sel(out / "before_viewx.sel")) | set(load_sel(out / "after_viewx.sel")))
        (out / "view_union.sel").write_text("\n".join(union) + ("\n" if union else ""))
        print(f"view: {len(union)} object(s) after matching unmatched ports")
    else:
        print(f"view: ports already match ({' '.join(sorted(bp)) or 'none'})")
    with (out / "seeds.ys").open("a") as f:
        f.write(f"select -set view -read {out / 'view_union.sel'}\n")


def render_stage(yosys, nlsvg, have_dot, out, top, stage, colors):
    show = ""
    if have_dot:
        show = (
            f"show -format svg -prefix {out / f'{stage}_show'} -notitle -width -signed "
            + (
                "-color crimson @moved -color orange @collateral @view"
                if stage == "before"
                else "-color forestgreen @moved -color forestgreen @added @view"
            )
            + "\n"
        )
    yosys_on(
        yosys,
        out,
        top,
        stage,
        (out / "seeds.ys").read_text().rstrip()
        + f"\n{show}submod -copy -noclean -name diffview @view\nselect -clear\nselect diffview\nwrite_json -selected {out / f'{stage}.json'}",
    )
    svg, jsn = out / f"{stage}.svg", out / f"{stage}.json"
    if nlsvg and jsn.exists():
        subprocess.run(
            [str(nlsvg), str(jsn), "-o", str(svg)], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False
        )
        if svg.exists():
            colorize_svg(svg, stage, colors)
            rasterize(svg, 2)
    rasterize(out / f"{stage}_show.svg", 1.5)


def render_entry(yosys, nlsvg, have_dot, design, top, args, refuse, out):
    retime, flops, cuts = parse_move(args)
    out.mkdir(parents=True, exist_ok=True)
    rc, log = yosys_p(
        yosys,
        f"read_verilog -icells {design}\nhierarchy -top {top}\ncheck -assert\n"
        f"write_rtlil -sort {out / 'before.il'}\nwrite_json {out / 'before_full.json'}\n{retime}\ncheck -assert\n"
        f"write_rtlil -sort {out / 'after.il'}\nwrite_json {out / 'after_full.json'}\n"
        f"tee -q -o {out / 'scratch_refusal.txt'} scratchpad -get opt_retime.refusal",
    )
    for chunk in re.findall(r"Executing OPT_RETIME.*?(?:\n\n|\Z)", log, re.DOTALL):
        print(chunk.rstrip())
    reason = refusal_reason(log, out / "scratch_refusal.txt")
    if refuse:
        if not reason:
            raise RuntimeError("move succeeded, so this entry is stale\n" + log)
        (out / "refusal.txt").write_text(reason + "\n")
        print(f"refused: {reason}")
    elif rc:
        raise RuntimeError(log)
    elif reason:
        raise RuntimeError(f"unexpected refusal: {reason}")
    if not write_seeds(out, refuse, cuts, flops):
        return
    if not refuse:
        expand_view(yosys, out, top)
    colors = json.loads((out / "diff_colors.json").read_text())
    render_stage(yosys, nlsvg, have_dot, out, top, "before", colors)
    if not refuse:
        render_stage(yosys, nlsvg, have_dot, out, top, "after", colors)


def count_regs(path):
    cells = [c for m in json.loads(path.read_text())["modules"].values() for c in m["cells"].values()]
    ffs = [c for c in cells if c["type"].startswith(FF_COUNT)]
    return len(ffs), sum(len(c["connections"]["Q"]) for c in ffs)


def read_seeds(path):
    info = dict.fromkeys(("moved", "collateral", "added_cells", "added_wires", "deleted_cells", "changed_cells"), "")
    if path.exists():
        for line in path.read_text().splitlines():
            k, _, v = line.partition(":")
            if k in info:
                info[k] = v.strip()
    return info


def imgs(label, stages):
    body = "<tr>" + "".join(f"<td><img src='{label}/{s}.svg'></td>" for s in stages) + "</tr>"
    if (OUT_ROOT / label / f"{stages[0]}_show.svg").exists():
        body += (
            f"<tr><th align=left colspan={len(stages)} class=sub>with bus widths and port names</th></tr><tr>"
            + "".join(f"<td><img src='{label}/{s}_show.svg'></td>" for s in stages)
            + "</tr>"
        )
    return body


def write_html(rows, refused):
    h = [
        (
            "<html><head><style>body{font:14px -apple-system,sans-serif;margin:2em;max-width:1400px}"
            "h2{margin-top:2.5em;border-top:1px solid #ccc;padding-top:1em}"
            "td{vertical-align:top;padding:4px 12px}img{max-width:640px;border:1px solid #eee}"
            "th.sub{padding-top:1.5em;font-weight:normal;color:#666}code{background:#f4f4f4;padding:1px 4px}</style></head><body>"
        ),
        "<h1>opt_retime before / after (diff neighborhood)</h1>",
        (
            "<p>Each pair is the RTLIL-diff seed plus a combinational hop around it, then the union of those two cones. "
            "<span style='color:#c62828'>Red</span> is the flop being moved (before), "
            "<span style='color:#2e7d32'>green</span> after, "
            "<span style='color:#ef6c00'>orange</span> a sibling flop the merge deleted.</p>"
        ),
        (
            "<table><tr><th align=left>move</th><th align=left>registers</th><th align=left>register bits</th>"
            "<th align=left>moved</th><th align=left>collateral</th></tr>"
        ),
    ]
    for label, b, a, _, info in rows:
        h.append(
            f"<tr><td><code>{label}</code></td><td>{b[0]} &rarr; {a[0]}</td><td>{b[1]} &rarr; {a[1]}</td>"
            f"<td>{info['moved'] or '&mdash;'}</td><td>{info['collateral'] or '&mdash;'}</td></tr>"
        )
    h.append("</table>")
    for label, b, a, note, info in rows:
        added = " ".join(x for x in (info["added_cells"], info["added_wires"]) if x) or "(none)"
        h += [
            f"<h2>{label}</h2>",
            f"<p>{note} registers {b[0]} &rarr; {a[0]}, register bits {b[1]} &rarr; {a[1]}</p>",
            f"<p>moved <code>{info['moved'] or '(none)'}</code><br>collateral <code>{info['collateral'] or '(none)'}</code><br>added <code>{added}</code></p>",
            "<table><tr><th align=left>before</th><th align=left>after</th></tr>"
            + imgs(label, ("before", "after"))
            + "</table>",
        ]
    if refused:
        h += [
            "<h1 style='margin-top:3em;border-top:3px solid #999;padding-top:1em'>refused moves</h1>",
            (
                "<p>One picture each. Seeded from the named flop and cut. "
                "<span style='color:#c62828'>Red</span> is the flop that could not move.</p>"
            ),
            "<table><tr><th align=left>move</th><th align=left>registers</th><th align=left>reason</th></tr>",
        ]
        for label, reason, b, _ in refused:
            h.append(f"<tr><td><code>{label}</code></td><td>{b[0]} ({b[1]} bits)</td><td>{escape(reason)}</td></tr>")
        h.append("</table>")
        for label, reason, b, info in refused:
            h += [
                f"<h2>{label}</h2>",
                f"<p>{escape(reason)}<br>{b[0]} registers, {b[1]} register bits</p>",
                f"<p>could not move <code>{info['moved'] or '(none)'}</code></p>",
                "<table><tr><th align=left>netlist as the pass saw it</th></tr>"
                + imgs(label, ("before",))
                + "</table>",
            ]
    (OUT_ROOT / "index.html").write_text("\n".join(h + ["</body></html>"]))


def collect_rows():
    rows, refused = [], []
    for label in sorted(os.listdir(OUT_ROOT)):
        d = OUT_ROOT / label
        if not d.is_dir():
            continue
        seeds = read_seeds(d / "seeds.txt")
        full_b = d / "before_full.json" if (d / "before_full.json").exists() else d / "before.json"
        if (d / "refusal.txt").exists():
            refused.append((label, (d / "refusal.txt").read_text().strip(), count_regs(full_b), seeds))
            continue
        full_a = d / "after_full.json" if (d / "after_full.json").exists() else d / "after.json"
        note = ""
        log = OUT_ROOT / f"{label}.log"
        if log.exists():
            note = " ".join(
                ln.strip() for ln in log.read_text().splitlines() if ln.startswith(("Retimed", "Resizing", "Folded"))
            )
            if note:
                note += " "
        rows.append((label, count_regs(full_b), count_regs(full_a), note, seeds))
    return rows, refused


def run_one(yosys, nlsvg, have_dot, line, refuse):
    design, top, args = parse_row(line)
    label = ("refused_" if refuse else "") + label_for(top, args)
    out, logp, buf = OUT_ROOT / label, OUT_ROOT / f"{label}.log", StringIO()
    try:
        with redirect_stdout(buf), redirect_stderr(buf):
            print(f"=== {top}{' (refused)' if refuse else ''}: {args}")
            render_entry(yosys, nlsvg, have_dot, DESIGNS / design, top, args, refuse, out)
        if (out / "yosys.log").exists():
            logp.write_text((out / "yosys.log").read_text())
        return True, label, buf.getvalue(), ""
    except RuntimeError as err:
        if (out / "yosys.log").exists():
            logp.write_text((out / "yosys.log").read_text())
        return False, label, buf.getvalue() + str(err), str(logp)


def main():
    if len(sys.argv) != 1:
        sys.exit("usage: ./retime_gallery.py")
    yosys, have_dot, nlsvg = yosys_bin(), shutil.which("dot") is not None, netlistsvg()
    if not have_dot:
        print("no graphviz dot in PATH, skipping the width-annotated view", file=sys.stderr)
    shutil.rmtree(OUT_ROOT, ignore_errors=True)
    OUT_ROOT.mkdir(parents=True)
    failed = []
    jobs = [(ln, False) for ln in MOVES] + [(ln, True) for ln in REFUSALS]
    with ProcessPoolExecutor(max_workers=WORKERS) as pool:
        futs = [pool.submit(run_one, yosys, nlsvg, have_dot, ln, refuse) for ln, refuse in jobs]
        for fut in as_completed(futs):
            ok, label, text, logp = fut.result()
            sys.stdout.write(text)
            if not ok:
                failed.append((label, logp))
    if failed:
        for label, logp in failed:
            print(f"  entry failed, see {logp} (index.html not written)", file=sys.stderr)
        sys.exit(1)
    rows, refused = collect_rows()
    write_html(rows, refused)
    print(f"\n{'move':<40} {'registers':<12} {'register bits':<16} collateral")
    for label, b, a, _, info in rows:
        print(f"{label:<40} {b[0]} -> {a[0]:<6} {b[1]} -> {a[1]:<10} {info['collateral'] or '-'}")
    if refused:
        print(f"\n{'refused':<40} reason")
        for label, reason, _, _ in refused:
            print(f"{label:<40} {reason}")
    print(f"\n{OUT_ROOT / 'index.html'}")


if __name__ == "__main__":
    main()
