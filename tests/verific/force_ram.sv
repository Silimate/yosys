module top(input clk, input we, input [3:0] wa, ra, input [7:0] wd, output [7:0] rd);
	typedef struct packed { logic [3:0] hi; logic [3:0] lo; } entry_t;
	(* force_ram *) entry_t forced [0:15];
	entry_t plain [0:15];
	always @(posedge clk) if (we) begin
		forced[wa] <= wd;
		plain[wa] <= wd;
	end
	assign rd = forced[ra] ^ plain[ra];
endmodule
