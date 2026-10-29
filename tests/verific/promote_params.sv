// FN and BASE come from the loop index and only supply values, so they become ports, and so do
// the localparams computed from them. MODE picks a generate branch, so it stays a parameter.
module bank #(parameter FN = 0, parameter BASE = 16'h0, parameter MODE = 0) (
	input clk, input rst, input [7:0] fn, input [31:0] addr, input [7:0] wdata, input we,
	output reg [7:0] q, output hit, output [7:0] tag
);
	localparam [31:0] NEXT = BASE + 8'h04;
	localparam ID = FN * 2 + 1;
	assign hit = fn == FN && (addr == BASE || addr == NEXT);
	always @(posedge clk)
		if (rst) q <= MODE ? 8'hff : 8'h00;
		else if (we && hit) q <= wdata;
	if (MODE) begin : g_odd
		leaf #(.K(ID)) u_leaf (.k(tag));
	end else begin : g_even
		assign tag = ~ID;
	end
endmodule

module leaf #(parameter K = 0) (output [7:0] k);
	assign k = K;
endmodule

// RST is a flop's asynchronous reset value, so its copies stay apart
module rbank #(parameter RST = 0) (input clk, input rst, input d, output reg [7:0] q);
	always @(posedge clk or posedge rst)
		if (rst) q <= RST;
		else q <= {q[6:0], d};
endmodule

// Non-ANSI ports, overridden and connected by position. LO's values are 32 bits wide in the loop
// but 8 bits where u_lone takes its default, so it stays a parameter.
module match (a, y, z);
	parameter IDX = 0;
	parameter LO = 8'd0;
	input [7:0] a;
	output y, z;
	assign y = a == IDX;
	assign z = a > LO;
endmodule

module top (
	input clk, input rst, input [7:0] fn, input [31:0] addr, input [7:0] wdata, input we,
	output [16*8-1:0] q, output [15:0] hit, output [16*8-1:0] tag, output [16*8-1:0] rq,
	output [15:0] eq, output [15:0] gt, output eq0, output gt0
);
	for (genvar i = 0; i < 16; i++) begin : g
		bank #(.FN(i), .BASE(16'h1000 + i * 16'h100), .MODE(i % 2)) u_bank (
			.clk(clk), .rst(rst), .fn(fn), .addr(addr), .wdata(wdata), .we(we),
			.q(q[i*8 +: 8]), .hit(hit[i]), .tag(tag[i*8 +: 8]));
		rbank #(.RST(i)) u_rbank (.clk(clk), .rst(rst), .d(we), .q(rq[i*8 +: 8]));
		match #(i, i * 8) u_match (addr[7:0], eq[i], gt[i]);
	end
	match u_lone (addr[7:0], eq0, gt0);
endmodule
