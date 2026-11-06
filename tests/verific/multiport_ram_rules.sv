module top(input clk, input rst, input we, input [1:0] wa, ra, input [7:0] wd, output [7:0] rd);
	reg [7:0] mem [0:3];
	always @(posedge clk)
		if (rst) mem <= '{default: 0};
		else if (we) mem[wa] <= wd;
	assign rd = mem[ra];
endmodule

module plain_ram(input clk, input we, input [1:0] wa, ra, input [7:0] wd, output [7:0] rd);
	reg [7:0] mem [0:3];
	always @(posedge clk) if (we) mem[wa] <= wd;
	assign rd = mem[ra];
endmodule
