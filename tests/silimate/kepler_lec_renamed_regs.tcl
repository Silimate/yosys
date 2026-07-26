# kepler_lec: renamed sequential instances force SEC auto-mode
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

set gold_v [file join [pwd] kepler_lec_renamed_gold.v]
set gate_v [file join [pwd] kepler_lec_renamed_gate.v]
set fh [open $gold_v w]
puts $fh {
module top(input clk, input d, output q);
  reg r_gold;
  always @(posedge clk) r_gold <= d;
  assign q = r_gold;
endmodule
}
close $fh
set fh [open $gate_v w]
puts $fh {
module top(input clk, input d, output q);
  reg r_gate;
  always @(posedge clk) r_gate <= d;
  assign q = r_gate;
endmodule
}
close $fh

log -header "kepler_lec renamed regs -> SEC"
log -push
design -reset
read_verilog $gold_v
hierarchy -top top
yosys proc; opt_clean
design -save gold_src

design -reset
read_verilog $gate_v
hierarchy -top top
yosys proc; opt_clean
design -save gate_src

design -reset
design -copy-from gold_src -as gold A:top
design -copy-from gate_src -as gate A:top
kepler_lec -mode auto -sec-engine pdr -k 4 -assert {*}$exe_args gold gate
scratchpad -assert kepler_lec.mode sec
scratchpad -assert kepler_lec.result equivalent
log -pop
file delete -force $gold_v $gate_v
puts "PASS kepler_lec_renamed_regs"
