#!/usr/bin/env python3
"""Fail unless every pyosys wheel in the given directories is a Release build.

pyosys/build/local_backend.py takes the CMake build type from `-C cmake=...`
and no longer defaults it. Without it CMake builds unoptimized, and the wheel
still imports and passes its tests while every pass runs ~10x slower. Yosys
records the build type in its version string, e.g.
"Yosys 0.69+ (git sha1 bc2a4680f, Release, AppleClang ...)", so read it back
out of each wheel's libyosys.
"""

import pathlib
import re
import sys
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


def main(dirs):
	wheels = [w for d in dirs for w in sorted(pathlib.Path(d).glob("*.whl"))]
	if not wheels:
		sys.exit(f"no wheels found in {' '.join(dirs)}")
	bad = []
	for wheel in wheels:
		kind = build_type(wheel)
		print(f"{wheel.name}: build type {kind!r}")
		if kind != "Release":
			bad.append(wheel.name)
	if bad:
		sys.exit("not a Release build (pass -C cmake=-DCMAKE_BUILD_TYPE=Release): " + ", ".join(bad))


if __name__ == "__main__":
	main(sys.argv[1:])
