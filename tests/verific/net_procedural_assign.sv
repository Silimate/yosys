// An output port declared without a type is a net; always_ff still drives it in Verilator
module top (
	input logic clk,
	input logic a, b,
	output qa,
	output qb,
	output qc
);
	always_ff @(posedge clk) begin
		{qa, qb} <= {a, b};
		qc <= a ^ b;
	end
endmodule

module ref_top (
	input logic clk,
	input logic a, b,
	output logic qa,
	output logic qb,
	output logic qc
);
	always_ff @(posedge clk) begin
		{qa, qb} <= {a, b};
		qc <= a ^ b;
	end
endmodule
