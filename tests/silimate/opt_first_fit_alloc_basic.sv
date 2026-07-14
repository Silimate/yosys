// Clean identity gather (no guard, no compaction, LSB-first): slot j reads the
// j-th enabled request lane's data; saturates at NB (later leaders dropped).
module opt_first_fit_alloc_basic #(
  parameter int N = 8,
  parameter int NB = 4,
  parameter int W = 8
)(
  input  logic         clk,
  input  logic [N-1:0] req,
  input  logic [W-1:0] data [N],
  output logic [W-1:0] slot_q [NB]
);
  logic [W-1:0] slot_n [NB];
  int cnt;
  always_comb begin
    for (int j = 0; j < NB; j++) slot_n[j] = '0;
    cnt = 0;
    for (int k = 0; k < N; k++) begin
      if (req[k]) begin
        if (cnt < NB) slot_n[cnt] = data[k];
        cnt = cnt + 1;
      end
    end
  end
  always_ff @(posedge clk)
    for (int j = 0; j < NB; j++) slot_q[j] <= slot_n[j];
endmodule
