// Adder chain: two flopped operands into $add, then $sub against a third.
//   fa -\
//         a0 ($add) -> b0 ($buf) -> a1 ($sub) -> fq
//   fb -/                            ^
//   fc ------------------------------/
// Every net is single-fanout, so this is the smallest design that needs a
// non-$buf cut. Forward moves it covers:
//   -flop fa -cut a0 -forward : fa and fb merge into one flop on the sum
//   -flop fb -cut a0 -forward : same move, entering a0 on B instead of A
//   -flop fa -cut b0 -forward : $buf and $add mixed in one chain
//   -flop fa -cut a1 -forward : the longest chain here, merging at two cells
//                               (covered by opt_retime_sub.ys)

module retime_add (clk, a, b, c, q);
  input clk;
  input [7:0] a, b, c;
  output [7:0] q;
  wire [7:0] ra, rb, rc, s0, s0b, s1;

  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fc (.CLK(clk), .D(c), .Q(rc));

  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(ra), .B(rb), .Y(s0));
  $buf #(.WIDTH(8))
    b0 (.A(s0), .Y(s0b));
  $sub #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a1 (.A(s0b), .B(rc), .Y(s1));

  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(s1), .Q(q));
endmodule
