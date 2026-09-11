// Comparator and reduction: wide in, one bit out, so a move changes how many
// flop bits the design costs.
//   fa -\
//        c_eq ($eq) -> e -\
//   fb -/                  g0 ($and) -> bg ($buf) -> fq
//   fc -> r_or ($reduce_or) -> r -/
// Every net is single-fanout. Moves it should cover once the pass grows past
// buffers:
//   -flop fq -cut g0 -backward   : 1 flop bit becomes 2
//   -flop fq -cut c_eq -backward : 1 flop bit becomes 16, across g0 and c_eq
//   -flop fc -cut r_or -forward  : 8 flop bits collapse to 1
//   -flop fa -cut c_eq -forward  : illegal unless fb moves too

module retime_cmp (clk, a, b, c, q);
  input clk;
  input [7:0] a, b, c;
  output q;
  wire [7:0] ra, rb, rc;
  wire e, r, g, gb;

  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fc (.CLK(clk), .D(c), .Q(rc));

  $eq #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(1), .A_SIGNED(0), .B_SIGNED(0))
    c_eq (.A(ra), .B(rb), .Y(e));
  $reduce_or #(.A_WIDTH(8), .Y_WIDTH(1), .A_SIGNED(0))
    r_or (.A(rc), .Y(r));
  $and #(.A_WIDTH(1), .B_WIDTH(1), .Y_WIDTH(1), .A_SIGNED(0), .B_SIGNED(0))
    g0 (.A(e), .B(r), .Y(g));
  $buf #(.WIDTH(1))
    bg (.A(g), .Y(gb));

  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(gb), .Q(q));
endmodule
