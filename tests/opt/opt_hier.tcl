yosys -import

# per each opt_hier_*.v source file, confirm flattening and hieropt+flattening
# are combinationally equivalent, both through the opt loop and with opt_hier
# running its own rounds to saturation
foreach fn [glob opt_hier_*.v] {
	foreach cmd {{opt -hier} {opt_hier -max_iter 0 -full -purge}} {
		log -header "Test $fn with $cmd"
		log -push
		design -reset

		read_verilog $fn
		hierarchy -auto-top
		prep -top top
		design -save start
		flatten
		design -save gold
		design -load start
		yosys {*}$cmd
		# check any instances marked `should_get_optimized_out` were
		# indeed optimized out
		select -assert-none a:should_get_optimized_out
		dump
		flatten
		design -save gate

		design -reset
		design -copy-from gold -as gold A:top
		design -copy-from gate -as gate A:top
		yosys rename -hide
		equiv_make gold gate equiv
		equiv_induct -ignore-unknown-cells equiv
		equiv_status -assert equiv

		log -pop
	}
}
