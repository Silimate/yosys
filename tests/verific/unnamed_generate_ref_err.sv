// Names in unnamed generate blocks that stay 'not declared' outside them, even under relaxed checking

// Two generate constructs declare 'x': which one is meant depends on the parameters
module two_constructs #(parameter W = 0) (input [3:0] a, output [3:0] y);
	generate
		if (W) begin
			wire [3:0] x = a;
		end
	endgenerate
	generate
		if (!W) begin
			wire [3:0] x = ~a;
		end
	endgenerate
	assign y = x;
endmodule

// A for-generate block's names need an index
module in_loop (input [3:0] a, output [3:0] y);
	generate
		for (genvar i = 0; i < 2; i = i + 1) begin
			wire [3:0] x = a + i;
		end
	endgenerate
	assign y = x;
endmodule

// The other branch of the generate-if the reference is in is never generated with it
module other_branch #(parameter W = 0) (input [3:0] a, output [3:0] y);
	generate
		if (W) begin
			wire [3:0] x = a;
			assign y = x;
		end else begin
			assign y = x;
		end
	endgenerate
endmodule

// A named generate block's names need its name
module named_block #(parameter W = 1) (input [3:0] a, output [3:0] y);
	generate
		if (W) begin : g
			wire [3:0] x = a;
		end
	endgenerate
	assign y = x;
endmodule
