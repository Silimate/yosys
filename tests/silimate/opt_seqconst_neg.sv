// Three pointers that must not fold, one per way the induction can fail. The first two
// reset asynchronously so that they do have a base case and are rejected by the
// inductive step itself rather than for want of a seed.
module opt_seqconst_neg (
    input  logic       clk,
    input  logic       rst,
    input  logic       wr,
    input  logic [4:0] load,
    output logic [4:0] skew,
    output logic [4:0] ext,
    output logic [4:0] noreset
  );

  // Stepped by 5, so no tail survives: bit 0 alternates.
  always_ff @(posedge clk or posedge rst)
    if (rst)     skew <= '0;
    else if (wr) skew <= 5'(skew + 5);

  // Aligned step, but an external load can put anything in the low bits.
  always_ff @(posedge clk or posedge rst)
    if (rst)     ext <= '0;
    else if (wr) ext <= 5'(ext + 8);
    else         ext <= load;

  // Aligned step and nothing else writes it, but with no reset there is no base
  // case: the initial value is unconstrained.
  always_ff @(posedge clk)
    if (wr) noreset <= 5'(noreset + 8);

endmodule
