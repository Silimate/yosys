// Yosys `read_verilog -sv` frontend variant of the clean identity gather.
// Uses packed flat ports (the yosys frontend does not accept unpacked array
// ports) but the same first-fit body, so the pass must fire on this lowering.
module opt_first_fit_alloc_yosys_basic #(
  parameter integer N = 8,
  parameter integer NB = 4,
  parameter integer W = 8
)(
  input  wire             clk,
  input  wire [N-1:0]     req,
  input  wire [N*W-1:0]   data_flat,
  output reg  [NB*W-1:0]  slot_q
);
  reg [W-1:0] slot_n [0:NB-1];
  integer j, k, cnt;
  always @* begin
    for (j = 0; j < NB; j = j + 1) slot_n[j] = {W{1'b0}};
    cnt = 0;
    for (k = 0; k < N; k = k + 1) begin
      if (req[k]) begin
        if (cnt < NB) slot_n[cnt] = data_flat[k*W +: W];
        cnt = cnt + 1;
      end
    end
  end
  always @(posedge clk)
    for (j = 0; j < NB; j = j + 1) slot_q[j*W +: W] <= slot_n[j];
endmodule
