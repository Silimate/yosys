#!/usr/bin/env bash
# sim reads each array dimension's declared direction from the order Verific gives the element
# ports it splits an array port into (tests/sim/array_port.v writes that order by hand). Import
# the real SystemVerilog here and replay dumps that flatten the arrays: -sim-cmp fails if an
# element is bound to any bits other than the ones SystemVerilog packs it into, and a missing
# element is fatal.
set -euo pipefail
YOSYS=${YOSYS:-../../build/yosys}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

cat > $tmp/array_ports.sv <<'EOT'
module array_port_1d (
  input  logic [2:0] coeffs [0:-2],
  input  logic [1:0] offs   [1:3],
  input  logic [3:0] asc    [-2:0],
  output logic [8:0]  coeffs_q,
  output logic [5:0]  offs_q,
  output logic [11:0] asc_q
);
  assign coeffs_q = {coeffs[0], coeffs[-1], coeffs[-2]};
  assign offs_q   = {offs[1], offs[2], offs[3]};
  assign asc_q    = {asc[-2], asc[-1], asc[0]};
endmodule

module array_port_2d (
  input  logic [3:0]  grid [1:0][-1:1],
  output logic [23:0] grid_q
);
  assign grid_q = {grid[1][-1], grid[1][0], grid[1][1], grid[0][-1], grid[0][0], grid[0][1]};
endmodule

// A packed 2-D port is split into the same element ports and packs the same way
module array_port_2d_packed (
  input  logic [1:0][-1:1][3:0] grid,
  output logic [23:0]           grid_q
);
  assign grid_q = grid;
endmodule
EOT

# sim converts a VCD to <tmpdir>/converted_<basename>.fst, so replay private copies under names
# the tests/sim runs of the same dumps do not use.
for shape in 1d_bits 1d_vector 2d_bits 2d_vector 2d_rows; do
	cp ../sim/array_port_$shape.vcd $tmp/verific_array_port_$shape.vcd
done

replay() {  # replay <module> <dump shape>
	$YOSYS -q -p "verific -sv $tmp/array_ports.sv; verific -import $1; prep -top $1
		select -assert-count 1 i:grid[1][-1] i:coeffs[-2] %u
		sim -r $tmp/verific_array_port_$2.vcd -scope tb.dut -sim-cmp -q"
}

replay array_port_1d 1d_bits
replay array_port_1d 1d_vector
replay array_port_2d 2d_bits
replay array_port_2d 2d_vector
replay array_port_2d 2d_rows
replay array_port_2d_packed 2d_bits
replay array_port_2d_packed 2d_rows
