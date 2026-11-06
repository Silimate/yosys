checker chk(input logic a);
endchecker

module top(input [3:0] a, output [3:0] y, output [3:0] z);
	function automatic [3:0] checker(input [3:0] v);
		return ~v;
	endfunction
	assign y = checker(a);
	assign z = checker /* comment before the call */ (y);
endmodule
