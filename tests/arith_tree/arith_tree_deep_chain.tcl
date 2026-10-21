yosys -import

# Operand arrival is found by walking back through driver cells, so a long
# combinational chain in front of the tree must not overflow the native stack.
# Sum y = m0 + d + e, where m0 comes out of a chain of muxes, mux i reading the
# output of mux i+1. Depth, not width, is what matters, so the chain is one bit
# wide to stay light. It is written as RTLIL, as no frontend unrolls it quickly.
set n 200000
set fd [file tempfile path arith_tree_deep_chain.il]
puts $fd "module \\top
  wire input 1 \\a
  wire input 2 \\b
  wire input 3 \\s
  wire width 32 input 4 \\d
  wire width 32 input 5 \\e
  wire width 32 output 6 \\y
  wire \\m$n
  connect \\m$n \\a"
for {set i [expr {$n - 1}]} {$i >= 0} {incr i -1} {
	puts $fd "  wire \\m$i
  cell \$mux \\mux$i
    parameter \\WIDTH 1
    connect \\A \\m[expr {$i + 1}]
    connect \\B \\b
    connect \\S \\s
    connect \\Y \\m$i
  end"
}
puts $fd {  wire width 32 \q
  cell $add \add0
    parameter \A_SIGNED 0
    parameter \B_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_WIDTH 32
    parameter \Y_WIDTH 32
    connect \A \m0
    connect \B \d
    connect \Y \q
  end
  cell $add \add1
    parameter \A_SIGNED 0
    parameter \B_SIGNED 0
    parameter \A_WIDTH 32
    parameter \B_WIDTH 32
    parameter \Y_WIDTH 32
    connect \A \q
    connect \B \e
    connect \Y \y
  end
end}
close $fd
try {
	read_rtlil $path
} finally {
	file delete $path
}

select -assert-count $n t:\$mux
arith_tree
select -assert-count $n t:\$mux
select -assert-count 1 t:\$fa
