#!/usr/bin/env python3

# Diff-neighborhood gallery for opt_retime. Run it:
#
#   ./retime_gallery.py
#
# Writes /tmp/retime_debug_diff_all/index.html.

import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
DESIGNS = HERE / "designs"
OUT_ROOT = Path("/tmp/retime_debug_diff_all")
NLSVG_DIR = Path("/tmp/retime_debug_netlistsvg")
HOPS = 3
CONE = True
CLEAN = False

EMPTY = "n:$__diff_empty__"
FF_TYPES = ("$dff", "$dffe", "$adff", "$sdff", "$adffe", "$sdffe", "$aldff", "$dlatch")
FF_COUNT = ("$dff", "$sdff", "$adff", "$aldff", "$_DFF", "$_SDFF", "$_ALDFF")

# (design, top, args) or (design, top, args, pre). Design paths are relative
# to designs/. A refusal is a REFUSALS entry, not a switch.
MOVES = [
	("opt_retime_buf.v", "retime_probe", "-flop f1 -cut b2 -forward"),
	("opt_retime_buf.v", "retime_probe", "-flop f1 -cut b3 -forward"),
	("opt_retime_buf.v", "retime_probe", "-flop f1 -cut b1 -backward"),
	("opt_retime_add.v", "retime_add", "-flop fa -cut a0 -forward"),
	("opt_retime_add.v", "retime_add", "-flop fb -cut a0 -forward"),
	("opt_retime_add.v", "retime_add", "-flop fa -cut b0 -forward"),
	("opt_retime_add.v", "retime_add", "-flop fa -cut a1 -forward"),
	("opt_retime_mux.v", "retime_mux", "-flop fa -cut m0 -forward"),
	("opt_retime_mux.v", "retime_mux", "-flop fs -cut m0 -forward"),
	("opt_retime_mux.v", "retime_mux", "-flop fa -cut b0 -forward"),
	("opt_retime_cmp.v", "retime_cmp", "-flop fc -cut r_or -forward"),
	("opt_retime_cmp.v", "retime_cmp", "-flop fa -cut c_eq -forward"),
	("opt_retime_cmp.v", "retime_cmp", "-flop fc -cut r_or -forward + -flop fa -cut g0 -forward"),
	("opt_retime_cmp.v", "retime_cmp", "-flop fq -cut g0 -backward"),
	("retime_debug_designs.v", "carryout", "-flop fa -cut a0 -forward"),
	("retime_debug_designs.v", "narrow", "-flop fa -cut a0 -forward"),
	("retime_debug_designs.v", "fullmul", "-flop fa -cut m0 -forward"),
	("retime_debug_designs.v", "divcut", "-flop fa -cut d0 -forward"),
	("retime_debug_designs.v", "pmuxcut", "-flop fa -cut m0 -forward"),
	("retime_debug_designs.v", "signedmul", "-flop fa -cut m0 -forward"),
	("retime_debug_designs.v", "bitwise", "-flop fa -cut o0 -forward"),
	("retime_debug_designs.v", "bitwise", "-flop fc -cut x0 -forward"),
	("retime_debug_designs.v", "notpath", "-flop fa -cut n0 -forward"),
	("retime_debug_designs.v", "zeroinit", "-flop fa -cut c_ne -forward + -flop fc -cut c_lt -forward + -flop fi -cut c_gt -forward + -flop fe -cut r_and -forward + -flop fg -cut r_xor -forward + -flop fh -cut r_bool -forward"),
	("opt_retime_shift.v", "retime_shift", "-flop famt -cut s_var -forward"),
	("opt_retime_shift.v", "retime_shift", "-flop fd -cut s_const -forward"),
	("opt_retime_shift.v", "retime_shift", "-flop fd -cut s_var -forward"),
	("retime_debug_designs.v", "onesinit", "-flop fa -cut c_xnor -forward + -flop fc -cut r_xnor -forward + -flop fd -cut c_le -forward + -flop fg -cut c_ge -forward"),
	("retime_debug_designs.v", "enops", "-flop fa -cut a0 -forward + -flop fc -cut m0 -forward"),
	("retime_debug_designs.v", "initmerge", "-flop fbuf -cut b1 -forward + -flop fa -cut a0 -forward + -flop fc -cut mm -forward"),
	("retime_debug_designs.v", "initresize", "-flop fr -cut r0 -forward + -flop fca -cut c0 -forward"),
	("retime_debug_designs.v", "rstfold", "-flop fn -cut n0 -forward + -flop fa -cut a0 -forward"),
	("retime_debug_designs.v", "finerst", "-flop ff -cut n0 -forward"),
	("retime_debug_designs.v", "arstfold", "-flop fa -cut o0 -forward"),
	("retime_debug_designs.v", "tapped", "-flop fa -cut a0 -forward"),
	("retime_debug_designs.v", "halfconst", "-flop fa -cut a0 -forward"),
	("retime_debug_designs.v", "sliced", "-flop fb -cut a0 -forward"),
	("retime_debug_designs.v", "sliced", "-flop f0 -cut a0 -forward"),
	("retime_debug_designs.v", "signedshift", "-flop fa -cut s0 -forward"),
	("retime_debug_designs.v", "signedleft", "-flop fa -cut s0 -forward"),
	("retime_debug_designs.v", "constops", "-flop fa -cut a_inc -forward + -flop fb -cut a_mask -forward"),
	("retime_debug_designs.v", "subdes", "-flop fa -cut s0 -forward"),
	("retime_debug_designs.v", "aldffeq", "-flop fs -cut e0 -forward"),
	("retime_debug_designs.v", "addc", "-flop f -cut a0 -backward"),
	("retime_debug_designs.v", "invcap", "-flop f -cut n0 -backward"),
	("retime_debug_designs.v", "andc", "-flop f -cut a0 -backward"),
	("retime_debug_designs.v", "andlive", "-flop f -cut a0 -backward"),
	("retime_debug_designs.v", "mulc", "-flop f -cut m0 -backward"),
	("retime_debug_designs.v", "muleven", "-flop f -cut m0 -backward"),
	("retime_debug_designs.v", "mullive", "-flop f -cut m0 -backward"),
	("retime_debug_designs.v", "muxa", "-flop f -cut u0 -backward"),
	("retime_debug_designs.v", "muxb", "-flop f -cut u0 -backward"),
	("retime_debug_designs.v", "muxrst", "-flop f -cut u0 -backward"),
	("retime_debug_designs.v", "unflopped", "-flop fq -cut a0 -backward"),
	("retime_debug_designs.v", "muxtree", "-flop f -cut u2 -backward"),
	("retime_debug_designs.v", "muxtree", "-flop f -cut u0 -backward"),
	("retime_debug_designs.v", "backfanout", "-flop fq -cut b0 -backward"),
	("retime_debug_designs.v", "sharedcone", "-flop f1 -cut a0 -backward"),
	("retime_debug_designs.v", "sharedcone", "-flop f1 -cut a0 -backward + -flop f2 -cut a0_dup -backward"),
	("retime_debug_designs.v", "shareddeep", "-flop fq -cut a0 -backward"),
	("retime_debug_designs.v", "fanout2", "-flop f1 -cut a0 -backward -all-fanouts"),
	("retime_debug_designs.v", "fanout3", "-flop f1 -cut a0 -backward -all-fanouts"),
	("retime_debug_designs.v", "fanoutdeep", "-flop f1 -cut a0 -backward -all-fanouts"),
	("retime_debug_designs.v", "gated", "-flop f1 -cut a0 -backward"),
	("retime_debug_designs.v", "gatedin", "-flop f1 -cut a0 -backward"),
	("retime_debug_designs.v", "gatedfwd", "-flop fa -cut a0 -forward"),
	("retime_debug_designs.v", "midcut", "-flop fa -cut n2 -forward"),
	("retime_debug_designs.v", "midtap", "-flop fa -cut n1 -forward"),
]

REFUSALS = [
	("retime_debug_designs.v", "unflopped", "-flop fa -cut a0 -forward"),
	("retime_debug_designs.v", "liveselect", "-flop fa -cut m0 -forward"),
	("retime_debug_designs.v", "enmix", "-flop fa -cut a0 -forward"),
	("retime_debug_designs.v", "rstmix", "-flop fa -cut a0 -forward"),
	("retime_debug_designs.v", "mixinit", "-flop fa -cut a0 -forward"),
	("retime_debug_designs.v", "fine", "-flop fa -cut a0 -forward"),
	("opt_retime_acc.v", "retime_acc", "-flop f_acc -cut a_acc -forward"),
	("opt_retime_buf.v", "retime_probe", "-flop f1 -cut b0 -backward"),
	("retime_debug_designs.v", "signedshift", "-flop fq -cut s0 -backward"),
	("retime_debug_designs.v", "backwide", "-flop fq -cut a0 -backward"),
	("retime_debug_designs.v", "selpath", "-flop f -cut u0 -backward"),
	("retime_debug_designs.v", "andmask", "-flop f -cut a0 -backward"),
	("retime_debug_designs.v", "mulevenodd", "-flop f -cut m0 -backward"),
	("retime_debug_designs.v", "allconst", "-flop f -cut a0 -backward"),
	("retime_debug_designs.v", "gatecut", "-flop fa -cut g0 -forward"),
	("retime_debug_designs.v", "aloadnet", "-flop fa -cut n0 -forward"),
	("retime_debug_designs.v", "sharedrecon", "-flop fq -cut a0 -backward"),
	("retime_debug_designs.v", "sharedouttap", "-flop f1 -cut a0 -backward"),
	("retime_debug_designs.v", "fanoutsr", "-flop f1 -cut a0 -backward -all-fanouts"),
	("retime_debug_designs.v", "fanouten", "-flop f1 -cut a0 -backward -all-fanouts"),
	("retime_debug_designs.v", "twogates", "-flop fa -cut a0 -forward"),
	("retime_debug_designs.v", "midtap", "-flop fa -cut n2 -forward"),
]


def unpack(entry):
	if len(entry) == 4:
		return entry
	design, top, args = entry
	return design, top, args, ""


def label_for(top, args):
	nmoves = args.split().count("+") + 1
	if nmoves > 2:
		return "%s_%d_moves" % (top, nmoves)
	text = "%s %s" % (top, args)
	text = text.replace("-flop ", "").replace("-cut ", "")
	text = text.replace(" + ", "_then_")
	text = text.replace("-", "")
	return "_".join(text.split())


def find_yosys():
	repo = HERE.parents[1]
	candidates = [
		repo / "build" / "yosys",
		repo.parent / "sili-yosys" / "build" / "yosys",
	]
	for path in candidates:
		if os.access(path, os.X_OK):
			return path.resolve()
	sys.exit("no yosys binary")


def parse_move_args(args):
	cmds = []
	cur = []
	flops = []
	cuts = []
	prev = ""
	for tok in args.split():
		if tok == "+":
			cmds.append("opt_retime %s;" % " ".join(cur))
			cur = []
		else:
			cur.append(tok)
		if prev == "-flop":
			flops.append(tok)
		if prev == "-cut":
			cuts.append(tok)
		prev = tok
	cmds.append("opt_retime %s;" % " ".join(cur))
	return " ".join(cmds), flops, cuts


def run_yosys(yosys, script, log_path=None, quiet=False):
	cmd = [str(yosys)]
	if quiet:
		cmd.append("-q")
	cmd.extend(["-p", script])
	result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
	text = result.stdout or ""
	if log_path is not None:
		log_path.write_text(text)
	return result.returncode, text


def run_yosys_file(yosys, ys_path):
	result = subprocess.run(
		[str(yosys), "-q", "-s", str(ys_path)],
		stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
	if result.returncode != 0:
		sys.stderr.write(result.stdout or "")
		sys.exit(result.returncode)


def first_line(log_text, prefix):
	for line in log_text.splitlines():
		if line.startswith(prefix):
			return line[len(prefix):].strip()
	return ""


def extract_refusal(log_text, scratch_path):
	if scratch_path.exists():
		lines = [ln.strip() for ln in scratch_path.read_text().splitlines()
			if ln.strip() and not ln.startswith("Executing ") and 'not set' not in ln]
		if lines:
			return " ".join(lines)
	reason = first_line(log_text, "Refused:")
	if reason:
		return reason
	return first_line(log_text, "ERROR:")


def unesc(name):
	return name[1:] if name.startswith("\\") else name


def is_ff(cell_text):
	typ = unesc(cell_text.split()[1])
	return typ in FF_TYPES or typ.startswith("$_DFF") or typ.startswith("$_SDFF") or typ.startswith("$_DLATCH")


def parse_rtlil(path):
	cells, wires, assigns = {}, {}, {}
	in_module = False
	in_cell = False
	cell_name = None
	cell_lines = []
	with path.open() as f:
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
	parts = ["c:%s" % n for n in kind_cells] + ["w:%s" % n for n in kind_wires]
	return " ".join(parts) if parts else EMPTY


def load_sel(path):
	if not path.exists():
		return []
	return [line.strip() for line in path.read_text().splitlines() if line.strip()]


def write_sel(path, names):
	path.write_text("\n".join(names) + ("\n" if names else ""))


def write_seeds(out, before_il, after_il, hops, cone, refuse, cuts, flops):
	ba, wa, aa = parse_rtlil(before_il)
	moved = list(dict.fromkeys(flops))
	if refuse:
		moved = [n for n in moved if n in ba]
		seed_cells = sorted(set(moved) | {c for c in cuts if c in ba})
		seed_wires = []
		add_c = del_c = ch_c = add_w = del_w = ch_w = collateral = []
	else:
		bb, wb, ab = parse_rtlil(after_il)
		add_c, del_c, ch_c = classify(ba, bb)
		add_w, del_w, ch_w = classify({**wa, **aa}, {**wb, **ab})
		seed_cells = sorted(set(add_c) | set(del_c) | set(ch_c))
		seed_wires = sorted(set(add_w) | set(del_w) | set(ch_w))
		moved = [n for n in moved if n in ba or n in bb]
		collateral = [n for n in del_c if n not in moved and is_ff(ba[n])]

	(out / "seeds.txt").write_text(
		"cells: %s\nwires: %s\nmoved: %s\ncollateral: %s\n"
		"added_cells: %s\ndeleted_cells: %s\nchanged_cells: %s\n"
		"added_wires: %s\ndeleted_wires: %s\n" % (
			" ".join(seed_cells), " ".join(seed_wires), " ".join(moved),
			" ".join(collateral), " ".join(add_c), " ".join(del_c),
			" ".join(ch_c), " ".join(add_w), " ".join(del_w)))
	(out / "diff_colors.json").write_text(json.dumps({
		"moved": moved, "collateral": collateral, "added": add_c + add_w}))

	if not seed_cells and not seed_wires:
		(out / "seeds.ys").write_text("")
		print("seeds: none (%s)" % ("no cells named" if refuse else "no structural RTLIL diff"))
		return False

	if refuse:
		# No diff to sit in the middle of a neighborhood, and the interesting
		# operand is often a sibling flop that a register-bounded cone drops.
		view = "select -set view *"
	elif hops <= 0:
		view = "select -set view @seed"
	elif cone:
		view = "select -set view @seed %%cie%d @seed %%coe%d %%u" % (hops, hops)
	else:
		view = "select -set view @seed %%x%d:-[CLK,C,EN]" % hops

	(out / "seeds.ys").write_text(
		"select -set seed %s\nselect -set moved %s\n"
		"select -set collateral %s\nselect -set added %s\n%s\n" % (
			sel(seed_cells, seed_wires), sel(moved), sel(collateral),
			sel(add_c, add_w), view))
	print("seeds: %d cell(s), %d wire(s)" % (len(seed_cells), len(seed_wires)))
	print("  moved:       %s" % (" ".join(moved) or "(none)"))
	print("  collateral:  %s" % (" ".join(collateral) or "(none)"))
	print("  added:       %s" % (" ".join(add_c + add_w) or "(none)"))
	return True


def colorize_svg(svg_path, stage, colors):
	moved = colors.get("moved") or []
	collateral = colors.get("collateral") or []
	added = colors.get("added") or []

	def css_ident(name):
		return "cell_" + re.sub(r"([^A-Za-z0-9_-])", lambda m: "\\%x " % ord(m.group(1)), name)

	def rules(names, stroke, fill):
		out = []
		for name in names:
			ident = css_ident(name)
			out.append("rect.%s, path.%s, circle.%s { stroke: %s; fill: %s; }" % (
				ident, ident, ident, stroke, fill))
			out.append("line.%s { stroke: %s; }" % (ident, stroke))
		return out

	if stage == "before":
		css = rules(moved, "#c62828", "#ffcdd2") + rules(collateral, "#ef6c00", "#ffe0b2")
	else:
		css = rules(moved, "#2e7d32", "#c8e6c9") + rules(added, "#2e7d32", "#c8e6c9")
	if not css:
		return
	text = svg_path.read_text()
	gt = text.find(">")
	if gt < 0:
		return
	svg_path.write_text(text[:gt + 1] + "\n<style>\n" + "\n".join(css) + "\n</style>\n" + text[gt + 1:])


def ensure_netlistsvg():
	nlsvg = NLSVG_DIR / "node_modules" / ".bin" / "netlistsvg"
	if nlsvg.exists() and os.access(nlsvg, os.X_OK):
		return nlsvg
	print("installing netlistsvg into %s (one time)" % NLSVG_DIR)
	NLSVG_DIR.mkdir(parents=True, exist_ok=True)
	subprocess.run(
		["npm", "install", "--silent", "--prefix", str(NLSVG_DIR), "netlistsvg"],
		check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
	return nlsvg


def json_ports(path):
	design = json.loads(path.read_text())
	module = next(iter(design["modules"].values()))
	return set(module.get("ports", {}))


def dump_view(yosys, out, top, stage, ys_in, sel_out):
	ys = out / ("dump_%s.ys" % stage)
	ys.write_text(
		"read_rtlil %s\ncd %s\n%s\nselect -write %s @view\n" % (
			out / ("%s.il" % stage), top, ys_in.read_text().rstrip(), sel_out))
	run_yosys_file(yosys, ys)


def dump_ports(yosys, out, top, stage, ys_in, json_out):
	ys = out / ("dump_%s_ports.ys" % stage)
	ys.write_text(
		"read_rtlil %s\ncd %s\n%s\n"
		"submod -copy -noclean -name diffview @view\n"
		"select -clear\nselect diffview\nwrite_json -selected %s\n" % (
			out / ("%s.il" % stage), top, ys_in.read_text().rstrip(), json_out))
	run_yosys_file(yosys, ys)


def rasterize(path, zoom):
	png = path.with_suffix(".png")
	if shutil.which("rsvg-convert") and path.exists():
		subprocess.run(
			["rsvg-convert", "-z", str(zoom), "-b", "white", "-o", str(png), str(path)],
			check=False)


def render_stage(yosys, nlsvg, have_dot, out, top, stage, colors):
	ys = out / ("render_%s.ys" % stage)
	lines = [
		"read_rtlil %s" % (out / ("%s.il" % stage)),
		"cd %s" % top,
		(out / "seeds.ys").read_text().rstrip(),
	]
	if have_dot:
		if stage == "before":
			lines.append(
				"show -format svg -prefix %s -notitle -width -signed "
				"-color crimson @moved -color orange @collateral @view" % (out / "before_show"))
		else:
			lines.append(
				"show -format svg -prefix %s -notitle -width -signed "
				"-color forestgreen @moved -color forestgreen @added @view" % (out / "after_show"))
	lines.extend([
		"submod -copy -noclean -name diffview @view",
		"select -clear",
		"select diffview",
		"write_json -selected %s" % (out / ("%s.json" % stage)),
	])
	ys.write_text("\n".join(lines) + "\n")
	run_yosys_file(yosys, ys)
	svg = out / ("%s.svg" % stage)
	jsn = out / ("%s.json" % stage)
	if nlsvg is not None and jsn.exists():
		subprocess.run([str(nlsvg), str(jsn), "-o", str(svg)],
			stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False)
		if svg.exists():
			colorize_svg(svg, stage, colors)
			rasterize(svg, 2)
	show_svg = out / ("%s_show.svg" % stage)
	if show_svg.exists():
		rasterize(show_svg, 1.5)


def expand_view(yosys, out, top):
	dump_view(yosys, out, top, "before", out / "seeds.ys", out / "before_view.sel")
	dump_view(yosys, out, top, "after", out / "seeds.ys", out / "after_view.sel")
	before, after = load_sel(out / "before_view.sel"), load_sel(out / "after_view.sel")
	union = sorted(set(before) | set(after))
	write_sel(out / "view_union.sel", union)
	print("view: %d object(s) (union of %d before, %d after)" % (
		len(union), len(before), len(after)))
	(out / "seeds_union.ys").write_text(
		(out / "seeds.ys").read_text().rstrip() + "\nselect -set view -read %s\n" % (
			out / "view_union.sel"))
	dump_ports(yosys, out, top, "before", out / "seeds_union.ys", out / "before_view.json")
	dump_ports(yosys, out, top, "after", out / "seeds_union.ys", out / "after_view.json")
	bp, ap = json_ports(out / "before_view.json"), json_ports(out / "after_view.json")
	xor = sorted(bp ^ ap)
	(out / "xor_ports.sel").write_text("".join("%s/%s\n" % (top, n) for n in xor))
	if xor:
		print("view: unmatched ports %s vs %s" % (
			" ".join(sorted(bp - ap)) or "(none)",
			" ".join(sorted(ap - bp)) or "(none)"))
		(out / "seeds_expand.ys").write_text(
			(out / "seeds_union.ys").read_text().rstrip() +
			"\nselect -set xorw -read %s\n"
			"select -set view @view @xorw %%x1:-[CLK,C,EN] %%u\n" % (out / "xor_ports.sel"))
		dump_view(yosys, out, top, "before", out / "seeds_expand.ys", out / "before_viewx.sel")
		dump_view(yosys, out, top, "after", out / "seeds_expand.ys", out / "after_viewx.sel")
		union = sorted(set(load_sel(out / "before_viewx.sel")) | set(load_sel(out / "after_viewx.sel")))
		write_sel(out / "view_union.sel", union)
		print("view: %d object(s) after matching unmatched ports" % len(union))
	else:
		print("view: ports already match (%s)" % (" ".join(sorted(bp)) or "none"))
	with (out / "seeds.ys").open("a") as f:
		f.write("select -set view -read %s\n" % (out / "view_union.sel"))


def render_entry(yosys, nlsvg, have_dot, design, top, args, pre, expect_refuse, out):
	retime, flops, cuts = parse_move_args(args)
	clean_cmd = "opt_clean" if CLEAN else ""
	out.mkdir(parents=True, exist_ok=True)
	script = "\n".join([
		"read_verilog -icells %s" % design,
		"hierarchy -top %s" % top,
		"check -assert",
		pre,
		"write_rtlil -sort %s" % (out / "before.il"),
		"write_json %s" % (out / "before_full.json"),
		retime,
		"check -assert",
		clean_cmd,
		"write_rtlil -sort %s" % (out / "after.il"),
		"write_json %s" % (out / "after_full.json"),
		"tee -q -o %s scratchpad -get opt_retime.refusal" % (out / "scratch_refusal.txt"),
	])
	rc, log_text = run_yosys(yosys, script, out / "yosys.log")
	for chunk in re.findall(r"Executing OPT_RETIME.*?(?:\n\n|\Z)", log_text, re.S):
		print(chunk.rstrip())
	reason = extract_refusal(log_text, out / "scratch_refusal.txt")
	if expect_refuse:
		if not reason:
			print("move succeeded, so this entry is stale", file=sys.stderr)
			print(log_text, file=sys.stderr)
			sys.exit(1)
		(out / "refusal.txt").write_text(reason + "\n")
		print("refused: %s" % reason)
	elif rc != 0:
		sys.stderr.write(log_text)
		sys.exit(rc if rc else 1)
	elif reason:
		print("unexpected refusal: %s" % reason, file=sys.stderr)
		sys.exit(1)

	after_il = out / "after.il"
	if not write_seeds(out, out / "before.il", after_il if after_il.exists() else out / "before.il",
			HOPS, CONE, expect_refuse, cuts, flops):
		return
	if not expect_refuse:
		expand_view(yosys, out, top)
	colors = json.loads((out / "diff_colors.json").read_text())
	render_stage(yosys, nlsvg, have_dot, out, top, "before", colors)
	if not expect_refuse:
		render_stage(yosys, nlsvg, have_dot, out, top, "after", colors)


def count_regs(path):
	design = json.loads(path.read_text())
	cells = [c for m in design["modules"].values() for c in m["cells"].values()]
	ffs = [c for c in cells if c["type"].startswith(FF_COUNT)]
	return len(ffs), sum(len(c["connections"]["Q"]) for c in ffs)


def read_seeds(path):
	info = {"moved": "", "collateral": "", "added_cells": "", "added_wires": "",
		"deleted_cells": "", "changed_cells": ""}
	if not path.exists():
		return info
	for line in path.read_text().splitlines():
		key, _, val = line.partition(":")
		if key in info:
			info[key] = val.strip()
	return info


def esc(s):
	return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def write_html(root, rows, refused):
	html = [
		"<html><head><style>",
		"body{font:14px -apple-system,sans-serif;margin:2em;max-width:1400px}",
		"h2{margin-top:2.5em;border-top:1px solid #ccc;padding-top:1em}",
		"td{vertical-align:top;padding:4px 12px}img{max-width:640px;border:1px solid #eee}",
		"th.sub{padding-top:1.5em;font-weight:normal;color:#666}",
		"code{background:#f4f4f4;padding:1px 4px}",
		"</style></head><body>",
		"<h1>opt_retime before / after (diff neighborhood)</h1>",
		"<p>Each pair is the RTLIL-diff seed plus a combinational hop around it, "
		"then the union of those two cones so both pictures share the same window. "
		"<span style='color:#c62828'>Red</span> is the flop being moved (before), "
		"<span style='color:#2e7d32'>green</span> is that same flop after it hops, "
		"<span style='color:#ef6c00'>orange</span> is a sibling flop the merge deleted.</p>",
		"<table><tr><th align=left>move</th><th align=left>registers</th>"
		"<th align=left>register bits</th><th align=left>moved</th>"
		"<th align=left>collateral</th></tr>",
	]
	for label, before, after, _, info in rows:
		html.append(
			"<tr><td><code>%s</code></td><td>%d &rarr; %d</td><td>%d &rarr; %d</td>"
			"<td>%s</td><td>%s</td></tr>" % (
				label, before[0], after[0], before[1], after[1],
				info["moved"] or "&mdash;", info["collateral"] or "&mdash;"))
	html.append("</table>")
	for label, before, after, note, info in rows:
		html.append("<h2>%s</h2>" % label)
		html.append("<p>%s registers %d &rarr; %d, register bits %d &rarr; %d</p>" % (
			note, before[0], after[0], before[1], after[1]))
		html.append(
			"<p>moved <code>%s</code><br>collateral <code>%s</code><br>added <code>%s</code></p>" % (
				info["moved"] or "(none)", info["collateral"] or "(none)",
				" ".join(x for x in (info["added_cells"], info["added_wires"]) if x) or "(none)"))
		html.append("<table><tr><th align=left>before</th><th align=left>after</th></tr>"
			"<tr><td><img src='%s/before.svg'></td><td><img src='%s/after.svg'></td></tr>" % (
				label, label))
		if (root / label / "before_show.svg").exists():
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
			"and the cut it could not reach is in the same view. "
			"<code>retime_debug_designs.v</code> says what each one is showing; the "
			"reasons below are verbatim from the pass.</p>")
		html.append("<table><tr><th align=left>move</th><th align=left>registers</th>"
			"<th align=left>reason</th></tr>")
		for label, reason, before, _ in refused:
			html.append("<tr><td><code>%s</code></td><td>%d (%d bits)</td><td>%s</td></tr>" % (
				label, before[0], before[1], esc(reason)))
		html.append("</table>")
		for label, reason, before, info in refused:
			html.append("<h2>%s</h2>" % label)
			html.append("<p>%s<br>%d registers, %d register bits</p>" % (
				esc(reason), before[0], before[1]))
			html.append("<p>could not move <code>%s</code></p>" % (info["moved"] or "(none)"))
			html.append("<table><tr><th align=left>netlist as the pass saw it</th></tr>"
				"<tr><td><img src='%s/before.svg'></td></tr>" % label)
			if (root / label / "before_show.svg").exists():
				html.append("<tr><th align=left class=sub>with bus widths and port names</th></tr>"
					"<tr><td><img src='%s/before_show.svg'></td></tr>" % label)
			html.append("</table>")
	html.append("</body></html>")
	(root / "index.html").write_text("\n".join(html))


def collect_rows(root):
	rows = []
	refused = []
	for label in sorted(os.listdir(root)):
		d = root / label
		if not d.is_dir():
			continue
		reason_path = d / "refusal.txt"
		seeds = read_seeds(d / "seeds.txt")
		if reason_path.exists():
			full_b = d / "before_full.json"
			if not full_b.exists():
				full_b = d / "before.json"
			refused.append((label, reason_path.read_text().strip(), count_regs(full_b), seeds))
			continue
		full_b = d / "before_full.json"
		full_a = d / "after_full.json"
		if not full_b.exists():
			full_b, full_a = d / "before.json", d / "after.json"
		note = ""
		log_path = root / (label + ".log")
		if log_path.exists():
			for line in log_path.read_text().splitlines():
				if line.startswith(("Retimed", "Resizing", "Folded")):
					note += line.strip() + " "
		rows.append((label, count_regs(full_b), count_regs(full_a), note, seeds))
	return rows, refused


def run_catalog(yosys, nlsvg, have_dot, catalog, expect_refuse):
	for entry in catalog:
		design, top, args, pre = unpack(entry)
		label = label_for(top, args)
		if expect_refuse:
			label = "refused_" + label
		print("=== %s%s: %s" % (top, " (refused)" if expect_refuse else "", args))
		out = OUT_ROOT / label
		log_path = OUT_ROOT / (label + ".log")
		try:
			render_entry(yosys, nlsvg, have_dot, DESIGNS / design, top, args, pre,
				expect_refuse, out)
		except SystemExit:
			print("  entry failed, see %s (index.html not written)" % log_path, file=sys.stderr)
			raise
		# Persist the per-entry chatter next to the pictures.
		entry_log = (out / "yosys.log").read_text() if (out / "yosys.log").exists() else ""
		log_path.write_text(entry_log)


def main():
	if len(sys.argv) != 1:
		sys.exit("usage: ./retime_gallery.py")
	yosys = find_yosys()
	have_dot = shutil.which("dot") is not None
	if not have_dot:
		print("no graphviz dot in PATH, skipping the width-annotated view", file=sys.stderr)
	nlsvg = ensure_netlistsvg()
	if OUT_ROOT.exists():
		shutil.rmtree(OUT_ROOT)
	OUT_ROOT.mkdir(parents=True)
	run_catalog(yosys, nlsvg, have_dot, MOVES, False)
	run_catalog(yosys, nlsvg, have_dot, REFUSALS, True)
	rows, refused = collect_rows(OUT_ROOT)
	write_html(OUT_ROOT, rows, refused)
	print()
	print("%-40s %-12s %-16s %s" % ("move", "registers", "register bits", "collateral"))
	for label, before, after, _, info in rows:
		print("%-40s %-12s %-16s %s" % (
			label, "%d -> %d" % (before[0], after[0]),
			"%d -> %d" % (before[1], after[1]), info["collateral"] or "-"))
	if refused:
		print()
		print("%-40s %s" % ("refused", "reason"))
		for label, reason, _, _ in refused:
			print("%-40s %s" % (label, reason))
	print()
	print(OUT_ROOT / "index.html")


if __name__ == "__main__":
	main()
