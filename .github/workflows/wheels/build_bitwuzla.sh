#!/bin/bash
# Builds Bitwuzla, the SMT solver the lec pass proves cut miters with, into $1/bin/bitwuzla, linking
# GMP and MPFR statically so the binary runs wherever the wheel does. The Linux image builds it on
# Ubuntu instead (manylinux.Dockerfile): CentOS 7's GMP and MPFR are too old for it.
set -ex
GMP=6.3.0 MPFR=4.2.1 BITWUZLA=0.9.1
mkdir -p "$1" && prefix=$(cd "$1" && pwd)
src=$(mktemp -d)
cd "$src"
curl -fsSL https://ftp.gnu.org/gnu/gmp/gmp-$GMP.tar.xz | tar -xJ
(cd gmp-$GMP && ./configure --prefix="$prefix" --disable-shared --enable-static --enable-cxx && make -j"$(getconf _NPROCESSORS_ONLN)" install)
curl -fsSL https://ftp.gnu.org/gnu/mpfr/mpfr-$MPFR.tar.xz | tar -xJ
(cd mpfr-$MPFR && ./configure --prefix="$prefix" --disable-shared --enable-static --with-gmp="$prefix" && make -j"$(getconf _NPROCESSORS_ONLN)" install)
git clone -q --depth 1 -b $BITWUZLA https://github.com/bitwuzla/bitwuzla
cd bitwuzla
PKG_CONFIG_PATH="$prefix/lib/pkgconfig" ./configure.py --static --prefix "$prefix"
ninja -C build install
rm -rf "$src"
"$prefix/bin/bitwuzla" --version
