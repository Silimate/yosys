// FN and BASE come from the loop index and only supply values, so they become ports, and so do
// the localparams computed from them. MODE picks a generate branch, so it stays a parameter.
module bank #(parameter FN = 0, parameter BASE = 16'h0, parameter MODE = 0) (
	input clk, input rst, input [7:0] fn, input [31:0] addr, input [7:0] wdata, input we,
	output reg [7:0] q, output hit, output [7:0] tag, output [1:0] par
);
	localparam [31:0] NEXT = BASE + 8'h04;
	localparam ID = FN * 2 + 1;
	assign hit = fn == FN && (addr == BASE || addr == NEXT);
	always @(posedge clk)
		if (rst) q <= MODE ? 8'hff : 8'h00;
		else if (we && hit) q <= wdata;
	// Two copies per bank, so pair only promotes by following FN
	for (genvar j = 0; j < 2; j++) begin : g_pair
		pair #(.K((FN + j) % 2)) u_pair (.k(par[j]));
	end
	if (MODE) begin : g_odd
		leaf #(.K(ID)) u_leaf (.k(tag));
	end else begin : g_even
		assign tag = ~ID;
	end
endmodule

module leaf #(parameter K = 0) (output [7:0] k);
	assign k = K;
endmodule

module pair #(parameter K = 0) (output k);
	assign k = K;
endmodule

// wrap overrides A with a 64-bit value, so P's values are 64 bits though A's default is 8, and
// its port is 64 bits wide
module wrap #(parameter A = 8'd0) (output [16*64-1:0] y);
	for (genvar j = 0; j < 16; j++) begin : g
		wide #(.P(A + j)) u (.y(y[j*64 +: 64]));
	end
endmodule

module wide #(parameter P = 0) (output [63:0] y);
	assign y = P;
endmodule

// RST is a flop's asynchronous reset value, so its copies stay apart, and TAG alone as a port
// would merge none of them
module rbank #(parameter RST = 0, parameter TAG = 0) (input clk, input rst, input d, output reg [7:0] q);
	always @(posedge clk or posedge rst)
		if (rst) q <= RST;
		else q <= {q[6:0], d ^ TAG[0]};
endmodule

// V's values are 32 bits in the loop but 64 bits at u_mixed, so it stays a parameter
module mixed #(parameter V = 0) (output [63:0] y);
	assign y = V;
endmodule

// FN picks a generate branch, so shell's copies stay apart and it keeps BASE too. core still
// elaborates once, its port connected to shell's parameter.
module shell #(parameter FN = 0, parameter BASE = 0) (input [31:0] addr, output hit, output first);
	if (FN == 0) begin : g_first
		assign first = 1'b1;
	end else begin : g_rest
		assign first = 1'b0;
	end
	core #(.BASE(BASE)) u_core (.addr(addr), .hit(hit));
endmodule

module core #(parameter BASE = 0) (input [31:0] addr, output hit);
	assign hit = addr[31:16] == BASE[31:16];
endmodule

// Non-ANSI ports, overridden and connected by position. u_lone takes IDX's default.
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
	output [15:0] eq, output [15:0] gt, output eq0, output gt0, output [16*2-1:0] par, output [16*64-1:0] wy,
	output [16*64-1:0] my, output [63:0] my1, output [15:0] chit, output [15:0] cfirst
);
	for (genvar i = 0; i < 16; i++) begin : g
		bank #(.FN(i), .BASE(16'h1000 + i * 16'h100), .MODE(i % 2)) u_bank (
			.clk(clk), .rst(rst), .fn(fn), .addr(addr), .wdata(wdata), .we(we),
			.q(q[i*8 +: 8]), .hit(hit[i]), .tag(tag[i*8 +: 8]), .par(par[i*2 +: 2]));
		rbank #(.RST(i), .TAG(i)) u_rbank (.clk(clk), .rst(rst), .d(we), .q(rq[i*8 +: 8]));
		match #(i) u_match (addr[7:0], eq[i], gt[i]);
		mixed #(.V(i)) u_mixed (.y(my[i*64 +: 64]));
		// A base address assembled from the index, which only Verific's evaluation can size
		localparam [31:0] OFF = 32'h0 + i;
		shell #(.FN(i), .BASE({4'd0, OFF[11:0], 16'h0})) u_shell (.addr(addr), .hit(chit[i]), .first(cfirst[i]));
	end
	mixed #(.V(64'h1_0000_0000)) u_mixed (.y(my1));
	match u_lone (addr[7:0], eq0, gt0);
	wrap #(.A(64'h1_0000_0000)) u_wrap (.y(wy));
endmodule
