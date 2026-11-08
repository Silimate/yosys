#!/bin/bash
# Builds Bitwuzla, the SMT solver the lec pass proves cut miters with, into $1/bin/bitwuzla, GMP and
# MPFR linked statically (on Linux the whole binary is static) so it runs wherever the wheel does,
# and puts its license and those of what it links in $1/share/licenses/bitwuzla
set -ex
GMP=6.3.0 MPFR=4.2.1 BITWUZLA=0.9.1
mkdir -p "$1" && prefix=$(cd "$1" && pwd)
jobs=$(getconf _NPROCESSORS_ONLN)
src=$(mktemp -d)
cd "$src"
curl -fsSL https://ftp.gnu.org/gnu/gmp/gmp-$GMP.tar.xz | tar -xJ
(cd gmp-$GMP && ./configure --prefix="$prefix" --disable-shared --enable-static --enable-cxx && make -j$jobs install)
curl -fsSL https://ftp.gnu.org/gnu/mpfr/mpfr-$MPFR.tar.xz | tar -xJ
(cd mpfr-$MPFR && ./configure --prefix="$prefix" --disable-shared --enable-static --with-gmp="$prefix" && make -j$jobs install)
git clone -q --depth 1 -b $BITWUZLA https://github.com/bitwuzla/bitwuzla
(cd bitwuzla && PKG_CONFIG_PATH="$prefix/lib/pkgconfig" ./configure.py --static --prefix "$prefix" && ninja -C build install)

lic="$prefix/share/licenses/bitwuzla"
mkdir -p "$lic"
cp bitwuzla/COPYING "$lic/bitwuzla.txt"
cp bitwuzla/subprojects/cadical*/LICENSE "$lic/cadical.txt"
cp bitwuzla/subprojects/symfpu*/LICENSE "$lic/symfpu.txt"
cp gmp-$GMP/COPYING.LESSERv3 "$lic/lgpl-3.0.txt"
cp gmp-$GMP/COPYINGv3 "$lic/gpl-3.0.txt"
cat > "$lic/README" <<NOTE
bitwuzla is Bitwuzla $BITWUZLA (https://github.com/bitwuzla/bitwuzla, MIT; bitwuzla.txt), with
CaDiCaL (cadical.txt) and SymFPU (symfpu.txt) built in, linked statically against GMP $GMP
(https://gmplib.org) and MPFR $MPFR (https://www.mpfr.org), both LGPL-3.0-or-later
(lgpl-3.0.txt, which builds on gpl-3.0.txt). To use another GMP or MPFR, rebuild it from these
sources with .github/workflows/wheels/build_bitwuzla.sh from https://github.com/Silimate/yosys.
NOTE
rm -rf "$src"
"$prefix/bin/bitwuzla" --version
