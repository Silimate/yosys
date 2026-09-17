# A design-wide miss prints at most 100 unbound-object warnings, then one line for the rest;
# -d prints every one.
yosys -import

set n 103
set il "module \\top\n  wire input 1 \\clk\n"
for {set i 0} {$i < $n} {incr i} {
	append il "  wire \\q$i\n"
	append il "  attribute \\rtl_bind \"o$i/1\[0\]\"\n"
	append il "  cell \$dff \\ff$i\n    parameter \\CLK_POLARITY 1\n    parameter \\WIDTH 1\n"
	append il "    connect \\CLK \\clk\n    connect \\D \\q$i\n    connect \\Q \\q$i\n  end\n"
}
append il "end\n"
set path "reg_rename_status_cap_tmp.il"
set f [open $path w]
puts -nonewline $f $il
close $f
read_rtlil $path
file delete $path
hierarchy -top top
design -save generated

logger -expect warning "Cannot place 1 bit\\(s\\) of 1-bit object o\[0-9\]+, .*not in the waveform" 100
logger -expect warning "3 more object\\(s\\) left 3 Q bit\\(s\\) unbound; rerun reg_rename with -d to list every one" 1
logger -expect log "Bound 0 flop\\(s\\); unstamped 0, object absent $n, bit unplaced 0" 1
reg_rename -waveform reg_rename_status_instances.vcd -scope tb.dut
logger -check-expected
select -assert-count $n a:rtl_bind_status=absent

design -load generated
logger -expect warning "Cannot place 1 bit\\(s\\) of 1-bit object o\[0-9\]+, .*not in the waveform" $n
reg_rename -d -waveform reg_rename_status_instances.vcd -scope tb.dut
logger -check-expected
