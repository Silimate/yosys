// dsel-rooted regression: the allocation result is materialised as a per-lane
// slot INDEX (lane_slot[i] = rank of lane i among enabled lanes, saturating at
// NB). This is the shape the original split-root path already handles, so it must
// keep rewriting via that path (independent of the gather-root anchor) and must
// not be double-claimed.
module opt_first_fit_alloc_dsel #(
  parameter int N = 16,
  parameter int NB = 8
)(
  input  logic [N-1:0]          en,
  output logic [$clog2(NB)-1:0] slot [N]
);
  logic [$clog2(NB):0] cnt;
  always_comb begin
    cnt = 0;
    for (int i = 0; i < N; i++) begin
      slot[i] = '0;
      if (en[i]) begin
        if (cnt < NB) slot[i] = cnt[$clog2(NB)-1:0];
        cnt = cnt + 1;
      end
    end
  end
endmodule
