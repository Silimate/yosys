yosys -import

# A record the caller keeps in opt_dff.changed keeps what it held, and opt_hier -sat adds
# a line per module each fold changes: in hier_sat_narrow.v, `fast` once and `slow` once
# per stage of its 20-stage line. The caller's own `\fast` line is no fold of this call,
# so opt_hier still optimizes `fast` only twice (see opt_hier_sat.ys).
read_verilog hier_sat_narrow.v
hierarchy -top top
yosys proc
scratchpad -set opt_dff.changed {\fast}
logger -expect log {Optimizing module fast\.} 2
# -max_iter only bounds a broken run: this one settles after 3 rounds
opt_hier -max_iter 10 -sat
logger -check-expected
scratchpad -assert opt_hier.saturated true

# A command returns the scratchpad's result.string to Tcl
set record [scratchpad -copy opt_dff.changed result.string]
scratchpad -unset result.string
set lines [split $record "\n"]
set folds [lsort [concat [list {\fast}] [lrepeat 20 {\slow}]]]
if {[lindex $lines 0] ne {\fast} || [lsort [lrange $lines 1 end]] ne $folds} {
	error "unexpected opt_dff.changed record: [join $lines {, }]"
}
