#!/usr/bin/env python3
"""Fail unless every pyosys wheel in the given directories is a Release build with Tcl
and accurate license metadata.

pyosys/build/local_backend.py takes the CMake build type from `-C cmake=...`
and no longer defaults it. Without it CMake builds unoptimized, and the wheel
still imports and passes its tests while every pass runs ~10x slower. Yosys
records the build type in its version string, e.g.
"Yosys 0.69+ (git sha1 bc2a4680f, Release, AppleClang ...)", so read it back
out of each wheel's libyosys.

A wheel built without Tcl still imports and synthesizes, but has no sdc pass, so also
install each wheel in a fresh venv and run sdc, whose Tcl must start from the script
library the wheel carries as share/tcl.

auditwheel and delocate bundle shared libraries after the metadata is written, so check
that pyosys/NOTICE covers each one, that every License-File is in the wheel, and that
License-Expression parses.
"""

import email
import pathlib
import re
import subprocess
import sys
import tempfile
import zipfile

from packaging.licenses import InvalidLicenseExpression, canonicalize_license_expression

# The build type is a single word right after the hash. Without one the compiler
# follows instead ("..., AppleClang /usr/bin/c++ ..."), and this does not match.
BUILD_TYPE_RE = re.compile(rb"Yosys [0-9][^\x00(]* \(git sha1 [0-9a-f]{7,40}(?:-dirty)?, ([A-Za-z]+), ")

# Name prefixes of the bundled libraries pyosys/NOTICE covers
NOTICED_LIBS = ("libffi", "libtcl")


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


def has_tcl(wheel):
	with tempfile.TemporaryDirectory() as tmp:
		venv = pathlib.Path(tmp, "venv")
		subprocess.run([sys.executable, "-m", "venv", venv], check=True)
		py = venv / "bin" / "python"
		subprocess.run([py, "-m", "pip", "install", "-q", "--no-deps", wheel], check=True)
		run = subprocess.run([py, "-c", SDC_SMOKE], cwd=tmp, capture_output=True, text=True)
	out = run.stdout + run.stderr
	return run.returncode == 0 and "Tcl_Init() call failed" not in out and \
		re.search(r"^tcl_library=\S*/pyosys/share/tcl$", out, re.M) is not None


def license_problems(wheel):
	with zipfile.ZipFile(wheel) as zf:
		names = set(zf.namelist())
		metadata = next(n for n in names if n.endswith(".dist-info/METADATA"))
		meta = email.message_from_bytes(zf.read(metadata))
	problems = []
	try:
		canonicalize_license_expression(meta["License-Expression"] or "")
	except InvalidLicenseExpression as e:
		problems.append(str(e))
	files = meta.get_all("License-File", [])
	if "pyosys/NOTICE" not in files:
		problems.append("no License-File: pyosys/NOTICE")
	licenses = metadata.removesuffix("METADATA") + "licenses/"
	problems += [f"no {licenses}{f}" for f in files if licenses + f not in names]
	bundled = sorted(n.rsplit("/", 1)[1] for n in names if re.search(r"\.(dy)?libs/[^/]+$", n))
	problems += [f"bundles {lib}, which pyosys/NOTICE doesn't cover" for lib in bundled if not lib.startswith(NOTICED_LIBS)]
	return problems


def main(dirs):
	wheels = [w for d in dirs for w in sorted(pathlib.Path(d).glob("*.whl"))]
	if not wheels:
		sys.exit(f"no wheels found in {' '.join(dirs)}")
	bad = []
	for wheel in wheels:
		kind = build_type(wheel)
		tcl = has_tcl(wheel)
		print(f"{wheel.name}: build type {kind!r}, Tcl {'yes' if tcl else 'no'}")
		if kind != "Release":
			bad.append(f"{wheel.name} (not a Release build: pass -C cmake=-DCMAKE_BUILD_TYPE=Release)")
		if not tcl:
			bad.append(f"{wheel.name} (no Tcl: sdc failed or did not start Tcl from share/tcl)")
		bad += [f"{wheel.name} ({problem})" for problem in license_problems(wheel)]
	if bad:
		sys.exit("bad wheels: " + ", ".join(bad))


if __name__ == "__main__":
	main(sys.argv[1:])
