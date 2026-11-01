module child(input en, input [3:0] d, output [3:0] q);
	assign q = en ? d : 4'b0;
endmodule

module constants(input en, input [3:0] a, input [3:0] b, input [1:0] sel, input [7:4] hi, input [0:3] up,
		output [3:0] y, output z, output [3:0] w, output h, output u);
	child u_child(.en(en), .d(a), .q(y));
	assign z = sel[1] & b[0];
	assign w = sel[0] ? a : b;
	assign h = hi[4] | b[1];
	assign u = up[0] & b[2];
endmodule
