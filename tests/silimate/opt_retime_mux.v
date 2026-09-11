// Mux: the first design where a cut has a control port distinct from its data
// ports, and the first that is a DAG rather than a chain.
//   fa -> m0.A
//   fb -> m0.B   m0 ($mux) -> b0 ($buf) -> fq
//   fs -> m0.S
// Moves it should cover once the pass grows past buffers:
//   -flop fq -cut m0 -backward : must fan out onto A and B, and must NOT put
//                                a flop on S (or must flop S separately)
//   -flop fa -cut m0 -forward  : illegal unless fb moves too; fs stays put
//   -flop fs -cut m0 -forward  : select is not on the data path, must refuse
// TODO: add a $pmux design once $mux works; one-hot select changes the rules.

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
