# kepler_lec: detect inequivalence
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

set vfile [file join [pwd] kepler_lec_neq_dut.v]
set fh [open $vfile w]
puts $fh {
module gold(input a, input b, output y);
  assign y = a & b;
endmodule
module gate(input a, input b, output y);
  assign y = a | b;
endmodule
}
close $fh

log -header "kepler_lec detects difference"
log -push
design -reset
read_verilog $vfile
design -save all
design -reset
design -copy-from all -as gold gold
design -copy-from all -as gate gate
kepler_lec -mode lec -nocleanup {*}$exe_args gold gate
scratchpad -assert kepler_lec.result different
log -pop
file delete -force $vfile
puts "PASS kepler_lec_neq"
