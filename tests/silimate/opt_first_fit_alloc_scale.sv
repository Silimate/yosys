// Scaling stress for the compacted reconstruction: N=32 lanes into NB=4 slots
// with a strided/negated composite enable and entry-side compaction. Guards the
// budget/cap machinery against pathological blowup on a wide allocation while
// still exercising a real rewrite (the wider clean identity gather is capped by
// the older split-root path and is covered separately at N<=16).
module opt_first_fit_alloc_scale32 #(
  parameter int N = 32, parameter int NB = 4, parameter int W = 8,
  parameter int NR = 64
)(
  input  logic          clk,
  input  logic [NB-1:0] hit,
  input  logic [N-1:0]  lhit,
  input  logic [NR-1:0] req_vld,
  input  logic [W-1:0]  req_off [NR],
  output logic [W-1:0]  eoff_q [NB]
);
  logic [W-1:0] eoff [NB], eoff_n [NB];
  logic [N-1:0] lpick;
  logic         replaced;
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
