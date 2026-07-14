// FSM `case` guard + per-entry hit branch peeling, with two sibling gathers
// driven by one allocation: eoff_n (the first-fit draw) and entry_n (a hit-side
// touch). Only the pure alloc sub-node under the guards is re-driven; the FSM
// case and the hit mux stay intact. Mirrors track_texel's S_ACCUM arm.
typedef enum logic [1:0] { S_IDLE=2'd0, S_INIT=2'd1, S_ACCUM=2'd2 } ffa_st_e;
module opt_first_fit_alloc_fsm #(
  parameter int N = 8, parameter int NB = 4, parameter int W = 8, parameter int NR = 16
)(
  input  logic          clk,
  input  ffa_st_e       st_n,
  input  logic [NR-1:0] req_vld,
  input  logic [W-1:0]  req_off [NR],
  input  logic [W-1:0]  cmp [NB],
  output logic [W-1:0]  eoff_q [NB],
  output logic [W-1:0]  entry_q [NB]
);
  logic [W-1:0] eoff [NB], eoff_n [NB];
  logic [W-1:0] entry [NB], entry_n [NB];
  logic [NB-1:0] hitv;
  logic [N-1:0] lhit, lpick;
  logic         replaced;

  always_comb begin
    for (int j = 0; j < NB; j++) hitv[j] = (entry[j] != 0);
    for (int k = 0; k < N; k++) begin
      lhit[k] = 1'b0;
      for (int j = 0; j < NB; j++)
        if (hitv[j] && req_vld[k*2] && (eoff[j] == req_off[k*2])) lhit[k] = 1'b1;
    end
  end

  always_comb begin
    for (int j = 0; j < NB; j++) begin
      eoff_n[j]  = eoff[j];
      entry_n[j] = entry[j];
    end
    for (int k = 0; k < N; k++) lpick[k] = 1'b0;
    unique case (st_n)
      S_ACCUM: begin
        for (int j = 0; j < NB; j++) begin
          if (hitv[j]) begin
            entry_n[j] = cmp[j];               // hit-true: touch entry, not eoff
          end else begin
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
      default: ;
    endcase
  end
  always_ff @(posedge clk) for (int j = 0; j < NB; j++) begin
    eoff[j]  <= eoff_n[j];
    entry[j] <= entry_n[j];
  end
  always_comb for (int j = 0; j < NB; j++) begin
    eoff_q[j]  = eoff[j];
    entry_q[j] = entry[j];
  end
endmodule
