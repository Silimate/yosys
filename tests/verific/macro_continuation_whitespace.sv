`define SUM 1 \ 
	+ 2
module top(output [3:0] y);
	assign y = `SUM;
endmodule
