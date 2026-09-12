// Accumulator and incrementer: the combinational cone closes through the flop,
// so the retimed path is a cycle rather than a feed-forward pipeline.
//   fx -> rx -\
//              a_acc ($add) -> b_acc ($buf) -> f_acc ($sdff) -> acc
//        acc -/                                                  \-> b_out
//   a_cnt ($add with constant 1) -> f_cnt -> cnt -> b_cnt
// A register in a loop is always read at least twice (by the operator and by
// whatever observes it). Feed-forward extra readers get a leftover copy, but
// here the copy's D sits on the after-path of the cut, so the move is still
// refused: rewriting the cut would change the tap's input.
// f_acc has a synchronous reset on purpose: moving it across a_acc changes the
// value the accumulator resets to, so SRST_VALUE has to be adjusted. The pass
// folds reset values now (opt_retime_reset.ys), so what still blocks these
// moves is the loop, not the reset.
// Forward moves it should cover once the pass grows past buffers:
//   -flop f_acc -cut a_acc -forward : legal only if it stays inside the loop
//   -flop f_cnt -cut a_cnt -forward : same shape with a constant operand
//   -flop f_acc -cut b_acc -forward : wraps the loop, must not lose the reset

module retime_acc (clk, rst, x, acc_o, cnt_o);
  input clk, rst;
  input [7:0] x;
  output [7:0] acc_o;
  output [3:0] cnt_o;
  wire [7:0] rx, acc, sum, sumb;
  wire [3:0] cnt, cntn;

  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fx (.CLK(clk), .D(x), .Q(rx));

  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a_acc (.A(acc), .B(rx), .Y(sum));
  $buf #(.WIDTH(8))
    b_acc (.A(sum), .Y(sumb));
  $sdff #(.WIDTH(8), .CLK_POLARITY(1'b1), .SRST_POLARITY(1'b1), .SRST_VALUE(8'h00))
    f_acc (.CLK(clk), .SRST(rst), .D(sumb), .Q(acc));
  $buf #(.WIDTH(8))
    b_out (.A(acc), .Y(acc_o));

  $add #(.A_WIDTH(4), .B_WIDTH(1), .Y_WIDTH(4), .A_SIGNED(0), .B_SIGNED(0))
    a_cnt (.A(cnt), .B(1'b1), .Y(cntn));
  $dff #(.WIDTH(4), .CLK_POLARITY(1'b1))
    f_cnt (.CLK(clk), .D(cntn), .Q(cnt));
  $buf #(.WIDTH(4))
    b_cnt (.A(cnt), .Y(cnt_o));
endmodule
