// Array ports as Verific imports them: one input wire per element, named with the declared
// index (negative ones included) and numbered in declaration order. read_verilog keeps both the
// escaped names and the port order as written here, so these modules stand in for the split
// SystemVerilog below without needing Verific.
//
// Every output is its array packed the SystemVerilog way (left bound most significant), so
// `sim -sim-cmp` against a dump that records those outputs fails unless each element was bound
// to its own bits.

// logic [2:0] coeffs [0:-2];  negative low bound, declared [hi:lo]: [-2] is least significant
// logic [1:0] offs   [1:3];   positive low bound, declared [lo:hi]: [3] is least significant
// logic [3:0] asc    [-2:0];  negative low bound, declared [lo:hi]: [0] is least significant
module array_port_1d (
	input  wire [2:0] \coeffs[0] ,
	input  wire [2:0] \coeffs[-1] ,
	input  wire [2:0] \coeffs[-2] ,
	input  wire [1:0] \offs[1] ,
	input  wire [1:0] \offs[2] ,
	input  wire [1:0] \offs[3] ,
	input  wire [3:0] \asc[-2] ,
	input  wire [3:0] \asc[-1] ,
	input  wire [3:0] \asc[0] ,
	output wire [8:0] coeffs_q,
	output wire [5:0] offs_q,
	output wire [11:0] asc_q
);
	assign coeffs_q = {\coeffs[0] , \coeffs[-1] , \coeffs[-2] };
	assign offs_q = {\offs[1] , \offs[2] , \offs[3] };
	assign asc_q = {\asc[-2] , \asc[-1] , \asc[0] };
endmodule

// logic [3:0] grid [1:0][-1:1];  outer [hi:lo], inner [lo:hi] with a negative bound
module array_port_2d (
	input  wire [3:0] \grid[1][-1] ,
	input  wire [3:0] \grid[1][0] ,
	input  wire [3:0] \grid[1][1] ,
	input  wire [3:0] \grid[0][-1] ,
	input  wire [3:0] \grid[0][0] ,
	input  wire [3:0] \grid[0][1] ,
	output wire [23:0] grid_q
);
	assign grid_q = {\grid[1][-1] , \grid[1][0] , \grid[1][1] , \grid[0][-1] , \grid[0][0] , \grid[0][1] };
endmodule

// Shapes that bound before array elements were understood, kept as controls.
module array_port_controls (
	input  wire [7:0] vec,       // same name and width
	input  wire [1:0] bits,      // bit-blasted as bits[1], bits[0]
	input  wire [7:0] \din[1] ,  // only element of din [1:0] that is a port: 0-based word din[8..15]
	(* sim_const = "1010" *)
	input  wire [3:0] tied,      // parent tied it off; not in the dump
	(* sim_src = "tb.src", sim_src_bit = "2" *)
	input  wire [3:0] slice,     // bits [5:2] of another scope's vector
	output wire [25:0] ctl_q
);
	assign ctl_q = {vec, bits, \din[1] , tied, slice};
endmodule
