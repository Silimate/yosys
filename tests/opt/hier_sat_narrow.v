// One opt_hier round rewrites both leaves: `fast` folds its only register in the first
// fold, while `slow` folds one stage of a 20-stage line per fold, more than a round's 16.
module slow(input clk, input d, output q);
	reg [19:0] p;
	always @(posedge clk) p <= {p[18:0], d};
	assign q = p[19];
endmodule
module fast(input clk, input d, input x, output q);
	reg r;
	always @(posedge clk) r <= d & x;
	assign q = r;
endmodule
module top(input clk, input x, output qs, output qf);
	slow s(.clk(clk), .d(1'b0), .q(qs));
	fast f(.clk(clk), .d(1'b0), .x(x), .q(qf));
endmodule
