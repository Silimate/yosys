// Mux: the first design where a cut has a port that is not an operand, and the
// first that is a DAG rather than a chain.
//   fa -> m0.A
//   fb -> m0.B   m0 ($mux) -> b0 ($buf) -> fq
//   fs -> m0.S
// Every net is single-fanout. Forward moves it covers:
//   -flop fa -cut m0 -forward : folds fa, fb and fs into one register. S is
//                               not an exception: reg(S)?reg(B):reg(A) equals
//                               reg(S?B:A) only when all three are
//                               registered.
//   -flop fs -cut m0 -forward : the same move entered on S, which widens the
//                               surviving register from 1 bit to 8.
//   -flop fa -cut b0 -forward : $mux and $buf mixed in one chain
// TODO: add a $pmux design; a one-hot select changes the rules.

module retime_mux (clk, a, b, sel, q);
  input clk;
  input [7:0] a, b;
  input sel;
  output [7:0] q;
  wire [7:0] ra, rb, m, mb;
  wire rs;

  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) fs (.CLK(clk), .D(sel), .Q(rs));

  $mux #(.WIDTH(8))
    m0 (.A(ra), .B(rb), .S(rs), .Y(m));
  $buf #(.WIDTH(8))
    b0 (.A(m), .Y(mb));

  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(mb), .Q(q));
endmodule
