{ pkgs ? import <nixpkgs> {} }:
	let lib = pkgs.lib;
in
pkgs.mkShell {
	buildInputs = with pkgs; [
		ccache
		bison
		flex
		cmake
		eigen
		swig
		boost
		libedit
		pkg-config
		m4
		cmake
		ninja
		tcl
		libffi
		nodejs
		gawk
		gperf
		autoconf
		doxygen
		cudd
		zlib
		clang
		iverilog # tests
		gtkwave # vcd2fst
		(python3.withPackages(ps: with ps; [pip wheel pybind11 cxxheaderparser]))
		gtest
	];

	CMAKE_CXX_COMPILER_LAUNCHER = "ccache";
	cmakeFlags = with pkgs; [
		"-DCMAKE_C_COMPILER=clang"
		"-DCMAKE_CXX_COMPILER=clang++"
		"-DCMAKE_BUILD_TYPE=Debug"
		"-DCMAKE_CXX_FLAGS=-O0"
		"-DYOSYS_WITH_PYTHON:BOOL=ON"
	];
}
