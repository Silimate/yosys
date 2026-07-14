// Closest track_texel mirror (N=16, NB=4): hit[j]=OR_k mat and lhit[k]=OR_j mat
// share the SAME mat[j][k] = evld[j] & req_vld[2k] & (eoff[j]==req_off[2k]).
// Exercises the composite enable + sel_rev + eb_rev + ent_gated reconstruction.
module opt_first_fit_alloc_match #(
  parameter int N = 16, parameter int NB = 4, parameter int W = 8, parameter int NR = 32
)(
  input  logic          clk,
  input  logic [NR-1:0] req_vld,
  input  logic [W-1:0]  req_off [NR],
  output logic [W-1:0]  eoff_q [NB]
);
  logic [W-1:0] eoff [NB], eoff_n [NB];
  logic         evld [NB], evld_n [NB];
  logic         mat  [NB][N];
  logic [NB-1:0] hitv;
  logic [N-1:0]  lhit, lpick;
  logic          replaced;

  always_comb begin
    for (int j = 0; j < NB; j++) hitv[j] = 1'b0;
    for (int k = 0; k < N; k++) lhit[k] = 1'b0;
    for (int j = 0; j < NB; j++)
      for (int k = 0; k < N; k++) begin
        mat[j][k] = evld[j] && req_vld[k*2] && (eoff[j] == req_off[k*2]);
        if (mat[j][k]) begin hitv[j] = 1'b1; lhit[k] = 1'b1; end
      end
  end

  always_comb begin
    for (int j = 0; j < NB; j++) begin eoff_n[j] = eoff[j]; evld_n[j] = evld[j]; end
    for (int k = 0; k < N; k++) lpick[k] = 1'b0;
    for (int j = 0; j < NB; j++) begin
      if (!hitv[j]) begin
        replaced = 1'b0;
        for (int k = 0; k < N; k++) begin
          if (!lhit[k] && req_vld[k*2] && !lpick[k] && !replaced) begin
            evld_n[j] = 1'b1;
            eoff_n[j] = req_off[k*2];
            lpick[k]  = 1'b1;
            replaced  = 1'b1;
          end
        end
      end
    end
  end
  always_ff @(posedge clk) for (int j = 0; j < NB; j++) begin
    eoff[j] <= eoff_n[j];
    evld[j] <= evld_n[j];
  end
  always_comb for (int j = 0; j < NB; j++) eoff_q[j] = eoff[j];
endmodule
