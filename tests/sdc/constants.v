module child(input en, input [3:0] d, output [3:0] q);
	assign q = en ? d : 4'b0;
endmodule

module constants(input en, input [3:0] a, input [3:0] b, input [1:0] sel, output [3:0] y, output z, output [3:0] w);
	child u_child(.en(en), .d(a), .q(y));
	assign z = sel[1] & b[0];
	assign w = sel[0] ? a : b;
endmodule
