checker chk(input logic a);
endchecker

module top(input [3:0] a, output [3:0] y, output [3:0] z);
	function automatic [3:0] checker(input [3:0] v);
		checker = ~v;
	endfunction
	assign y = checker(a);
	assign z = checker /* comment before the call */ (y);
endmodule

module checker_var(input [3:0] a, output [5:0] y, output [5:0] y_ref);
	wire [3:0] checker, half;
	assign checker = a;
	assign half = checker / 2;
	assign y = {checker[0], half, checker <= 4'd7};
	assign y_ref = {a[0], a / 4'd2, a <= 4'd7};
endmodule
