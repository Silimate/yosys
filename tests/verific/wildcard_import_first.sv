// Two wildcard-imported packages declare the same names differently
package pkg_a;
	localparam int unsigned Width = 8;
	typedef enum logic [1:0] {A_IDLE, A_BUSY} state_e;
endpackage

package pkg_b;
	localparam int unsigned Width = 16;
	typedef enum logic [2:0] {B_IDLE, B_BUSY, B_DONE} state_e;
endpackage

// Each name resolves to the declaration from the first wildcard import that declares it
module first_a
	import pkg_a::*;
	import pkg_b::*;
(
	output logic [31:0] w,
	output logic [31:0] bits,
	output state_e st
);
	assign w = Width;
	assign bits = $bits(state_e);
	assign st = A_BUSY;
endmodule

module first_b
	import pkg_b::*;
	import pkg_a::*;
(
	output logic [31:0] w,
	output logic [31:0] bits
);
	assign w = Width;
	assign bits = $bits(state_e);
endmodule
