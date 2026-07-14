// Like the strided case but lhit is DERIVED internally (as in track_texel):
// lhit[k] = OR_j (hit[j] & req_vld[2k] & (eoff[j]==req_off[2k])). Exercises the
// composite-enable path where one enable factor is an internal (cut-leaf) bus.
module opt_first_fit_alloc_derived #(
  parameter int N = 8, parameter int NB = 4, parameter int W = 8,
  parameter int NR = 16
)(
  input  logic          clk,
  input  logic [NB-1:0] hit,
  input  logic [NR-1:0] req_vld,
  input  logic [W-1:0]  req_off [NR],
  output logic [W-1:0]  eoff_q [NB]
);
  logic [W-1:0] eoff [NB], eoff_n [NB];
  logic [N-1:0] lhit;
  logic [N-1:0] lpick;
  logic         replaced;

  always_comb begin
    for (int k = 0; k < N; k++) begin
      lhit[k] = 1'b0;
      for (int j = 0; j < NB; j++)
        if (hit[j] && req_vld[k*2] && (eoff[j] == req_off[k*2]))
          lhit[k] = 1'b1;
    end
  end

  always_comb begin
    for (int j = 0; j < NB; j++) eoff_n[j] = eoff[j];
    for (int k = 0; k < N; k++) lpick[k] = 1'b0;
    for (int j = 0; j < NB; j++) begin
      if (!hit[j]) begin
        replaced = 1'b0;
        for (int k = 0; k < N; k++) begin
          if (!lhit[k] && req_vld[k*2] && !lpick[k] && !replaced) begin
            eoff_n[j] = req_off[k*2];
            lpick[k]  = 1'b1;
            replaced  = 1'b1;
          end
        end
      end
    end
  end
  always_ff @(posedge clk) for (int j = 0; j < NB; j++) eoff[j] <= eoff_n[j];
  always_comb for (int j = 0; j < NB; j++) eoff_q[j] = eoff[j];
endmodule
