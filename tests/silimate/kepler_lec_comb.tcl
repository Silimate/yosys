# kepler_lec: combinational equivalence of identical AND cones
yosys -import

proc kepler_available {} {
	if {![catch {exec sh -c {command -v kepler-formal >/dev/null}}]} {
		return 1
	}
	if {[info exists ::env(KEPLER_FORMAL_EXE)] && [file executable $::env(KEPLER_FORMAL_EXE)]} {
		return 1
	}
	return 0
}

if {![kepler_available]} {
	puts "SKIP: kepler-formal not found on PATH / KEPLER_FORMAL_EXE"
	exit 0
}

set exe_args {}
if {[info exists ::env(KEPLER_FORMAL_EXE)] && $::env(KEPLER_FORMAL_EXE) ne ""} {
	set exe_args [list -exe $::env(KEPLER_FORMAL_EXE)]
}

set vfile [file join [pwd] kepler_lec_comb_dut.v]
set fh [open $vfile w]
puts $fh {
module top(input a, input b, output y);
  assign y = a & b;
endmodule
}
close $fh

log -header "kepler_lec combinational equivalent"
log -push
design -reset
read_verilog $vfile
hierarchy -top top
yosys proc; opt_clean
design -save base
design -reset
design -copy-from base -as gold A:top
design -copy-from base -as gate A:top
kepler_lec -mode lec -assert {*}$exe_args gold gate
scratchpad -assert kepler_lec.result equivalent
log -pop
file delete -force $vfile
puts "PASS kepler_lec_comb"
