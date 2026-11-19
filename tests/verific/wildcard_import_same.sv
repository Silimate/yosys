// Two wildcard-imported packages declare the same names the same way
package pkg_a;
	localparam int unsigned PaSize = 40;
	typedef logic [3:0] nibble_t;
endpackage

package pkg_b;
	// Physical address width
	localparam int unsigned PaSize = 40;
	typedef logic [3:0] nibble_t;
endpackage

module top
	import pkg_a::*;
	import pkg_b::*;
(
	input logic [PaSize-1:0] d,
	output logic [PaSize-1:0] q,
	output nibble_t n,
	output logic [31:0] width
);
	assign q = d;
	assign n = d[3:0];
	assign width = $bits(d) + $bits(n);
endmodule
