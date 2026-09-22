(* blackbox *)
module bb(input [3:0] a, output [3:0] y);
endmodule

// `en` is tied low at the top and reaches the only module that reads it through two
// modules that just hand it on. opt_hier carries a constant across one boundary per
// call, and substituting it into a pass-through module changes nothing else, so `opt
// -hier` only gets it to `leaf` if opt_hier reports the substitution as a change.
module leaf(input en, input [3:0] d, output [3:0] y);
	wire [3:0] t;
	(* should_get_optimized_out *)
	bb bb1(.a(d), .y(t));
	assign y = en ? t : 4'b0;
endmodule

module mid2(input en, input [3:0] d, output [3:0] y);
	leaf u(.en(en), .d(d), .y(y));
endmodule

module mid1(input en, input [3:0] d, output [3:0] y);
	mid2 u(.en(en), .d(d), .y(y));
endmodule

module top(input [3:0] d, output [3:0] y);
	mid1 u(.en(1'b0), .d(d), .y(y));
endmodule
