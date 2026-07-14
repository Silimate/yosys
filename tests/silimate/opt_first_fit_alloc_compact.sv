// Entry-side compaction + FF-Q hold: allocating entries (!hit[j]) draw the
// next available lane in order (lpick chain); occupied entries (hit[j]) hold
// their registered value. `avail` is a materialised static first-fit enable.
module opt_first_fit_alloc_compact #(
  parameter int N = 8, parameter int NB = 4, parameter int W = 8
)(
  input  logic          clk,
  input  logic [NB-1:0] hit,      // entry occupied -> hold its FF value
  input  logic [N-1:0]  avail,    // lane available (static first-fit enable)
  input  logic [W-1:0]  data [N],
  output logic [W-1:0]  eoff_q [NB]
);
  logic [W-1:0] eoff   [NB];
  logic [W-1:0] eoff_n [NB];
  logic [N-1:0] lpick;
  logic         replaced;
  always_comb begin
    for (int j = 0; j < NB; j++) eoff_n[j] = eoff[j];   // default: hold
    for (int k = 0; k < N; k++) lpick[k] = 1'b0;
    for (int j = 0; j < NB; j++) begin
      if (!hit[j]) begin
        replaced = 1'b0;
        for (int k = 0; k < N; k++) begin
          if (avail[k] && !lpick[k] && !replaced) begin
            eoff_n[j]  = data[k];
            lpick[k]   = 1'b1;
            replaced   = 1'b1;
          end
        end
      end
    end
  end
  always_ff @(posedge clk)
    for (int j = 0; j < NB; j++) eoff[j] <= eoff_n[j];
  always_comb
    for (int j = 0; j < NB; j++) eoff_q[j] = eoff[j];
endmodule
