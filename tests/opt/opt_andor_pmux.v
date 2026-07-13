module mixed_vector_decode(
	input  [2:0] sel0,
	input  [2:0] sel1,
	input  [3:0] a0,
	input  [3:0] b0,
	input  [3:0] c0,
	input  [3:0] a1,
	input  [3:0] b1,
	input  [3:0] c1,
	output [3:0] y0,
	output [3:0] y1
);
	assign {y1, y0} =
		({ {4{sel1 == 3'd1}}, {4{sel0 == 3'd1}} } & {a1, a0}) |
		({ {4{sel1 == 3'd2}}, {4{sel0 == 3'd2}} } & {b1, b0}) |
		({ {4{sel1 == 3'd3}}, {4{sel0 == 3'd3}} } & {c1, c0});
endmodule

module partial_vector_decode(
	input  [2:0] sel0,
	input  [2:0] sel1,
	input  [3:0] a0,
	input  [3:0] b0,
	input  [3:0] c0,
	input  [3:0] a1,
	input  [3:0] b1,
	input  [3:0] c1,
	input  [3:0] passthru,
	output [3:0] y0,
	output [3:0] y1
);
	wire [7:0] stage =
		({ {4{sel1 == 3'd1}}, {4{sel0 == 3'd1}} } & {a1, a0}) |
		({ {4{sel1 == 3'd2}}, {4{sel0 == 3'd2}} } & {b1, b0}) |
		({ {4{sel1 == 3'd3}}, {4{sel0 == 3'd3}} } & {c1, c0});

	assign y1 = stage[7:4];
	assign y0 = stage[3:0] | passthru;
endmodule

module tiny_decode(
	input  [1:0] sel,
	input        a,
	input        b,
	output       y
);
	assign y = ((sel == 2'd1) & a) | ((sel == 2'd2) & b);
endmodule

// 8 arms x 8 bits = 64 > min_pmux_bits; also exercises probe→full budget path.
// Avoid sel==0: proc's opt_expr rewrites that compare away from $eq.
module large_vector_decode(
	input  [3:0]  sel,
	input  [63:0] d,
	output [7:0]  y
);
	assign y =
		({8{sel == 4'd1}}  & d[ 7: 0]) |
		({8{sel == 4'd2}}  & d[15: 8]) |
		({8{sel == 4'd3}}  & d[23:16]) |
		({8{sel == 4'd4}}  & d[31:24]) |
		({8{sel == 4'd5}}  & d[39:32]) |
		({8{sel == 4'd6}}  & d[47:40]) |
		({8{sel == 4'd7}}  & d[55:48]) |
		({8{sel == 4'd8}}  & d[63:56]);
endmodule

// Wide AND/OR forest with no equality leaves: must stay a cheap no-op.
module stress_andor_no_eq(
	input  [127:0] a,
	input  [127:0] b,
	output [127:0] y
);
	assign y = (a & b) | (~a & ~b) | (a & ~b) | (~a & b);
endmodule
