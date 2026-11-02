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

// V's values are 32 bits in the loop but 64 bits at u_mixed. Every one is a non-negative number
// and V is only assigned whole, so a 64-bit port holds each copy's value and drives the same y.
module mixed #(parameter V = 0) (output [63:0] y);
	assign y = V;
endmodule

// Per-instance IDs written as 32-bit unsigned sums, the bare loop index, 8-bit values and the plain
// default, so their copies disagree on width and sign. ID is only read whole: assigned, compared
// with an unsigned input and passed on to a child, so a 32-bit unsigned port gives every copy the
// same results, and nleaf follows.
module node #(parameter ID = 1) (input [15:0] sel, output [15:0] id, output hit, output [15:0] cid, output reg [15:0] rid);
	assign id = ID;
	assign hit = sel == ID;
	always @* rid = ID;
	nleaf #(.ID(ID)) u_leaf (.id(cid));
endmodule

module nleaf #(parameter ID = 1) (output [15:0] id);
	assign id = ID;
endmodule

// The copies differ in width but are all signed, so a < V compares signed in each copy and in the
// 64-bit signed port alike
module lt #(parameter V = 0) (input signed [7:0] a, output y);
	assign y = a < V;
endmodule

// The values disagree on width, and a concatenation places the other bits by V's own width, so it
// stays a parameter
module cat #(parameter V = 0) (output [71:0] y);
	assign y = {V, 8'h5};
endmodule

// '1 fills the width of the comparison, so P == '1 holds for an 8-bit 8'hff but not at 32 bits
module ones #(parameter P = 0) (output y);
	assign y = P == '1;
endmodule

// One copy is overridden with '1, a 1-bit value that would fill a wider port with ones
module fill #(parameter V = 0) (output [15:0] y);
	assign y = V;
endmodule

// One copy's value is negative, which a wider type would extend differently
module neg #(parameter V = 0) (output [15:0] y);
	assign y = V;
endmodule

// The copies disagree on sign and a is signed, so the compare is signed in some copies and unsigned in
// others: no one port type keeps both
module scmp #(parameter V = 0) (input signed [7:0] a, output y);
	assign y = a < V;
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
	output [16*64-1:0] my, output [63:0] my1, output [15:0] chit, output [15:0] cfirst,
	output [19*16-1:0] nid, output [18:0] nhit, output [19*16-1:0] ncid, output [19*16-1:0] nrid,
	output [16:0] ly, output [17*72-1:0] cy, output [17*16-1:0] ny, output [16:0] sy,
	output [16:0] oy, output [17*16-1:0] fy
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
		if (i < 8) begin : g_lo
			node #(.ID(16'h100 + i)) u_node (.sel(addr[15:0]), .id(nid[i*16 +: 16]), .hit(nhit[i]),
				.cid(ncid[i*16 +: 16]), .rid(nrid[i*16 +: 16]));
		end else begin : g_hi
			node #(.ID(i)) u_node (.sel(addr[15:0]), .id(nid[i*16 +: 16]), .hit(nhit[i]),
				.cid(ncid[i*16 +: 16]), .rid(nrid[i*16 +: 16]));
		end
		lt #(.V(i)) u_lt (.a(wdata), .y(ly[i]));
		cat #(.V(i)) u_cat (.y(cy[i*72 +: 72]));
		neg #(.V(i - 1)) u_neg (.y(ny[i*16 +: 16]));
		scmp #(.V(i)) u_scmp (.a(wdata), .y(sy[i]));
		ones #(.P(32'd0 + i)) u_ones (.y(oy[i]));
		fill #(.V(i)) u_fill (.y(fy[i*16 +: 16]));
	end
	node #(.ID(8'd200)) u_node8 (.sel(addr[15:0]), .id(nid[16*16 +: 16]), .hit(nhit[16]),
		.cid(ncid[16*16 +: 16]), .rid(nrid[16*16 +: 16]));
	node u_node1 (.sel(addr[15:0]), .id(nid[17*16 +: 16]), .hit(nhit[17]), .cid(ncid[17*16 +: 16]), .rid(nrid[17*16 +: 16]));
	// 8 bits wide, the sum wraps to 44, which the 32-bit port must still see
	node #(.ID(8'd200 + 8'd100)) u_node9 (.sel(addr[15:0]), .id(nid[18*16 +: 16]), .hit(nhit[18]),
		.cid(ncid[18*16 +: 16]), .rid(nrid[18*16 +: 16]));
	lt #(.V(64'sd300)) u_lt (.a(wdata), .y(ly[16]));
	cat #(.V(16'h7)) u_cat (.y(cy[16*72 +: 72]));
	neg #(.V(8'd3)) u_neg (.y(ny[16*16 +: 16]));
	scmp #(.V(8'd9)) u_scmp (.a(wdata), .y(sy[16]));
	ones #(.P(8'hff)) u_ones (.y(oy[16]));
	fill #(.V('1)) u_fill (.y(fy[16*16 +: 16]));
	mixed #(.V(64'h1_0000_0000)) u_mixed (.y(my1));
	match u_lone (addr[7:0], eq0, gt0);
	wrap #(.A(64'h1_0000_0000)) u_wrap (.y(wy));
endmodule
