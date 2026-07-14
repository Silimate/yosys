// Near-miss shapes that are structurally mux/gather-like but are NOT a
// first-fit allocation, so the ConstEval fingerprint must reject them (no
// ffa_* network emitted).

// (1) Diagonal masked read: slot j reads its OWN lane j (not the j-th enabled
// lane). Same FF/mux skeleton as the basic gather, different function.
module opt_first_fit_alloc_diag #(
  parameter int N = 8, parameter int NB = 4, parameter int W = 8
)(
  input  logic         clk,
  input  logic [N-1:0] req,
  input  logic [W-1:0] data [N],
  output logic [W-1:0] slot_q [NB]
);
  logic [W-1:0] slot_n [NB];
  always_comb
    for (int j = 0; j < NB; j++)
      slot_n[j] = req[j] ? data[j] : '0;
  always_ff @(posedge clk)
    for (int j = 0; j < NB; j++) slot_q[j] <= slot_n[j];
endmodule

// (2) Non-exclusive draw: every allocating entry reads the FIRST available lane
// (no lpick chaining), so entries collide instead of compacting. Looks like the
// compact case but drops the exclusivity that makes it a first-fit.
module opt_first_fit_alloc_noexcl #(
  parameter int N = 8, parameter int NB = 4, parameter int W = 8
)(
  input  logic          clk,
  input  logic [NB-1:0] hit,
  input  logic [N-1:0]  avail,
  input  logic [W-1:0]  data [N],
  output logic [W-1:0]  eoff_q [NB]
);
  logic [W-1:0] eoff [NB], eoff_n [NB];
  logic         replaced;
  always_comb begin
    for (int j = 0; j < NB; j++) eoff_n[j] = eoff[j];
    for (int j = 0; j < NB; j++) begin
      if (!hit[j]) begin
        replaced = 1'b0;
        for (int k = 0; k < N; k++) begin
          if (avail[k] && !replaced) begin   // no !lpick[k]: not exclusive
            eoff_n[j] = data[k];
            replaced  = 1'b1;
          end
        end
      end
    end
  end
  always_ff @(posedge clk) for (int j = 0; j < NB; j++) eoff[j] <= eoff_n[j];
  always_comb for (int j = 0; j < NB; j++) eoff_q[j] = eoff[j];
endmodule
