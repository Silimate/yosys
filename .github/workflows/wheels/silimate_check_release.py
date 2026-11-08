#!/usr/bin/env python3
"""Fail unless every pyosys wheel in the given directories is a Release build with Tcl.

pyosys/build/local_backend.py takes the CMake build type from `-C cmake=...`
and no longer defaults it. Without it CMake builds unoptimized, and the wheel
still imports and passes its tests while every pass runs ~10x slower. Yosys
records the build type in its version string, e.g.
"Yosys 0.69+ (git sha1 bc2a4680f, Release, AppleClang ...)", so read it back
out of each wheel's libyosys.

A wheel built without Tcl still imports and synthesizes, but has no sdc pass, so also
install each wheel in a fresh venv and run sdc, whose Tcl must start from the script
library the wheel carries as share/tcl.

The lec pass proves cut miters with the Bitwuzla a release wheel carries beside yosys-abc,
and quietly skips that proof without one, so when the build was given one
(YOSYS_BITWUZLA_EXECUTABLE) check it is there, solves, and on macOS links only system
libraries (on Linux it is a static binary).
"""

import os
import pathlib
import re
import subprocess
import sys
import tempfile
import zipfile

# The build type is a single word right after the hash. Without one the compiler
# follows instead ("..., AppleClang /usr/bin/c++ ..."), and this does not match.
BUILD_TYPE_RE = re.compile(rb"Yosys [0-9][^\x00(]* \(git sha1 [0-9a-f]{7,40}(?:-dirty)?, ([A-Za-z]+), ")


def build_type(wheel):
	with zipfile.ZipFile(wheel) as zf:
		libs = [n for n in zf.namelist() if re.search(r"(^|/)libyosys[^/]*\.(so|dylib|pyd)$", n)]
		if not libs:
			return None
		match = BUILD_TYPE_RE.search(zf.read(libs[0]))
		return match.group(1).decode(errors="replace") if match else None


SDC_SMOKE = """
from pyosys import libyosys as ys
open("t.v", "w").write("module t(input a, output y); assign y = a; endmodule\\n")
open("t.sdc", "w").write("create_clock -name c -period 1\\nputs \\"tcl_library=[info library]\\"\\n")
ys.run_pass("read_verilog t.v; hierarchy -top t; sdc t.sdc", ys.Design())
"""


BITWUZLA_SMOKE = """
import os, subprocess, sys, pyosys
bitwuzla = os.path.join(os.path.dirname(pyosys.__file__), "bitwuzla")
query = "(declare-const x (_ BitVec 8))(assert (distinct (bvadd x x) (bvshl x #x01)))(check-sat)"
print("bitwuzla=" + subprocess.run([bitwuzla], input=query, capture_output=True, text=True).stdout.strip())
if sys.platform == "darwin":
	libs = subprocess.run(["otool", "-L", bitwuzla], capture_output=True, text=True).stdout.splitlines()[1:]
	print("nonsystem=" + " ".join(l.split()[0] for l in libs if not l.split()[0].startswith(("/usr/lib/", "/System/"))))
"""


def smoke(wheel):
	"""Whether the wheel's sdc starts Tcl, and whether its Bitwuzla solves on its own."""
	with tempfile.TemporaryDirectory() as tmp:
		venv = pathlib.Path(tmp, "venv")
		subprocess.run([sys.executable, "-m", "venv", venv], check=True)
		py = venv / "bin" / "python"
		subprocess.run([py, "-m", "pip", "install", "-q", "--no-deps", wheel], check=True)
		sdc = subprocess.run([py, "-c", SDC_SMOKE], cwd=tmp, capture_output=True, text=True)
		smt = subprocess.run([py, "-c", BITWUZLA_SMOKE], cwd=tmp, capture_output=True, text=True)
	out = sdc.stdout + sdc.stderr
	tcl = sdc.returncode == 0 and "Tcl_Init() call failed" not in out and \
		re.search(r"^tcl_library=\S*/pyosys/share/tcl$", out, re.M) is not None
	bitwuzla = smt.returncode == 0 and re.search(r"^bitwuzla=unsat$", smt.stdout, re.M) is not None and \
		re.search(r"^nonsystem=\S", smt.stdout, re.M) is None
	return tcl, bitwuzla


def main(dirs):
	wheels = [w for d in dirs for w in sorted(pathlib.Path(d).glob("*.whl"))]
	if not wheels:
		sys.exit(f"no wheels found in {' '.join(dirs)}")
	bad = []
	for wheel in wheels:
		kind = build_type(wheel)
		tcl, bitwuzla = smoke(wheel)
		print(f"{wheel.name}: build type {kind!r}, Tcl {'yes' if tcl else 'no'}, Bitwuzla {'yes' if bitwuzla else 'no'}")
		if kind != "Release":
			bad.append(f"{wheel.name} (not a Release build: pass -C cmake=-DCMAKE_BUILD_TYPE=Release)")
		if not tcl:
			bad.append(f"{wheel.name} (no Tcl: sdc failed or did not start Tcl from share/tcl)")
		if not bitwuzla and os.environ.get("YOSYS_BITWUZLA_EXECUTABLE"):
			bad.append(f"{wheel.name} (no Bitwuzla: pyosys/bitwuzla missing, failing, or linking non-system libraries)")
	if bad:
		sys.exit("bad wheels: " + ", ".join(bad))


if __name__ == "__main__":
	main(sys.argv[1:])
