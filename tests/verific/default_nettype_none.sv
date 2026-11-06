`default_nettype none
module top(input wire a, output wire y);
	assign w = ~a;
	assign y = w;
endmodule
