#!/bin/bash
# Builds the pyosys wheel into wheelhouse/, caching compiler output in .ccache/
set -ex

# Keep every path under the repo so ccache can match builds across runs
export TMPDIR=$PWD/.tmp CCACHE_DIR=$PWD/.ccache CCACHE_BASEDIR=$PWD CCACHE_MAXSIZE=1G CCACHE_COMPRESS=1
mkdir -p $TMPDIR
ccache -z

make -C verific/tclmain -j$(getconf _NPROCESSORS_ONLN)
python3 -m pip wheel . --no-build-isolation -Ccmake="-DCMAKE_BUILD_TYPE=Release -DYOSYS_COMPILER_LAUNCHER=ccache" -w wheelhouse
python3 .github/workflows/wheels/silimate_check_release.py wheelhouse
ccache -s
