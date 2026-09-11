// Shifters: fanout and width growth.
//   fd -> rd, read by both shifters (unique_reader() rejects this today)
//   famt -> ramt, a shift-amount bus that merges like any other data input
//   s_var  ($shr) keeps the width
//   s_const ($shl) grows 8 bits to 11, so a moved flop changes width
// Forward moves, both proved in opt_retime_shift.ys:
//   -flop fd -cut s_var -forward   : needs splitfanout first (rd has two
//                                    readers), then famt merges with it
//   -flop famt -cut s_var -forward : the same move entered on B, which widens
//                                    the surviving flop from 3 bits to 8
//   -flop fd -cut s_const -forward  : proved in opt_retime_const.ys instead,
//                                     since its amount is a constant and so
//                                     has no register to merge

module retime_shift (clk, d, amt, q0, q1);
  input clk;
  input [7:0] d;
  input [2:0] amt;
  output [7:0] q0;
  output [10:0] q1;
  wire [7:0] rd, sr;
  wire [2:0] ramt;
  wire [10:0] sl;

  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fd   (.CLK(clk), .D(d),   .Q(rd));
  $dff #(.WIDTH(3), .CLK_POLARITY(1'b1)) famt (.CLK(clk), .D(amt), .Q(ramt));

  $shr #(.A_WIDTH(8), .B_WIDTH(3), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    s_var (.A(rd), .B(ramt), .Y(sr));
  $shl #(.A_WIDTH(8), .B_WIDTH(3), .Y_WIDTH(11), .A_SIGNED(0), .B_SIGNED(0))
    s_const (.A(rd), .B(3'd3), .Y(sl));

  $dff #(.WIDTH(8),  .CLK_POLARITY(1'b1)) fq0 (.CLK(clk), .D(sr), .Q(q0));
  $dff #(.WIDTH(11), .CLK_POLARITY(1'b1)) fq1 (.CLK(clk), .D(sl), .Q(q1));
endmodule
