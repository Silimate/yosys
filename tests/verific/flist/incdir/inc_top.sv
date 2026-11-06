module inc_top(input a, output y);
	wire w;
	inc_leaf u0(.a(a), .y(w));
	inc_leaf2 u1(.a(w), .y(y));
endmodule
