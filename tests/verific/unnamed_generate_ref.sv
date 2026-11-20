// A net that only an unnamed generate block declares, used from outside the block. By the LRM the
// block is a scope, so the name is not visible there; Quartus resolves it, as 'genblk<n>.name'.

module inv4 (input [3:0] i, output [3:0] o);
	assign o = ~i;
endmodule

// Both branches of a generate-if declare 'x'
module uses #(parameter W = 0) (
	input clk,
	input [3:0] a,
	output [3:0] y,
	output [1:0] s,
	output reg [3:0] q,
	output [3:0] n,
	output [3:0] m
);
	generate
		if (W) begin
			wire [3:0] x = a + 4'd1;
		end else begin
			wire [3:0] x = a - 4'd1;
		end
	endgenerate
	assign y = x;                 // 'x' is not declared, by the LRM
	assign s = x[2:1];            // ... nor here
	always @(posedge clk) q <= x; // ... nor here
	inv4 u_n (.i(x), .o(n));      // An implicit net, by the LRM
	generate
		if (1) begin
			inv4 u_m (.i(x), .o(m)); // ... in another generate block too
		end
	endgenerate
endmodule

module uses_ref #(parameter W = 0) (
	input clk,
	input [3:0] a,
	output [3:0] y,
	output [1:0] s,
	output reg [3:0] q,
	output [3:0] n,
	output [3:0] m
);
	wire [3:0] x = W ? a + 4'd1 : a - 4'd1;
	assign y = x;
	assign s = x[2:1];
	always @(posedge clk) q <= x;
	assign n = ~x;
	assign m = ~x;
endmodule

// An else-if chain is one generate construct, and so is a case-generate: all their branches are genblk<n>.
// Blocks in a block are genblk<n>.genblk<m>.
module chain #(parameter A = 0) (
	input [3:0] a,
	output [3:0] y,
	output [3:0] z,
	output [3:0] w
);
	generate
		if (A == 0) begin
			wire [3:0] x = a;
		end else if (A == 1) begin
			wire [3:0] x = ~a;
		end else begin
			wire [3:0] x = a ^ 4'b0101;
		end
	endgenerate
	generate
		case (A)
			0: begin
				wire [3:0] c = a + 4'd2;
			end
			default: begin
				wire [3:0] c = a - 4'd2;
			end
		endcase
	endgenerate
	generate
		if (1) begin
			if (A != 1) begin
				wire [3:0] d = a & 4'b0011;
			end else begin
				wire [3:0] d = a | 4'b0011;
			end
		end
	endgenerate
	assign y = x;
	assign z = c;
	assign w = d;
endmodule

module chain_ref #(parameter A = 0) (
	input [3:0] a,
	output [3:0] y,
	output [3:0] z,
	output [3:0] w
);
	assign y = (A == 0) ? a : (A == 1) ? ~a : (a ^ 4'b0101);
	assign z = (A == 0) ? a + 4'd2 : a - 4'd2;
	assign w = (A != 1) ? (a & 4'b0011) : (a | 4'b0011);
endmodule

// A reference in the other branch of the generate-if that declares 'x' is to the implicit net 'x' the
// module-level port connection declares, so that net stays, for every reference to it
module kept #(parameter P = 0) (
	input [3:0] a,
	input [3:0] b,
	output [3:0] y,
	output [3:0] n
);
	inv4 u_k (.i(x), .o(n));
	generate
		if (P) begin
			wire [3:0] x = a;
		end else begin
			assign x = b;
			assign y = x;
		end
	endgenerate
endmodule

module kept_ref #(parameter P = 0) (
	input [3:0] a,
	input [3:0] b,
	output [3:0] y,
	output [3:0] n
);
	wire x = b[0]; // An implicit net is 1 bit wide
	assign y = x;
	assign n = ~{3'b000, x};
endmodule
