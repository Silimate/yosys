// Registers that only a conditional generate block declares, driven from outside the block under the
// same condition (MiSTer's hps_io.sv). When the block is not generated, the references go nowhere.
module top #(parameter P = 0) (
	input clk,
	input d,
	output o
);
	generate
		if (P) begin
			reg r, s;
			assign o = r ^ s;
		end else begin
			assign o = d;
		end
	endgenerate
	always @(posedge clk) begin
		if (P) {r, s} <= {d, 1'b1};
	end
endmodule

module ref_top #(parameter P = 0) (
	input clk,
	input d,
	output o
);
	reg r, s;
	always @(posedge clk) {r, s} <= {d, 1'b1};
	assign o = P ? r ^ s : d;
endmodule

// With no else branch, there is no genblk1 at all when the block is not generated
module no_else #(parameter P = 0) (
	input clk,
	input d,
	output reg q
);
	generate
		if (P) begin
			reg r;
			always @(posedge clk) r <= d;
		end
	endgenerate
	always @(posedge clk) q <= P ? r : d;
endmodule

module no_else_ref #(parameter P = 0) (
	input clk,
	input d,
	output reg q
);
	reg r;
	always @(posedge clk) r <= d;
	always @(posedge clk) q <= P ? r : d;
endmodule
