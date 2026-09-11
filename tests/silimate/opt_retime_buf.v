// Same topology as preqorsor tests/unit/eda/test_retime_candidates.py:
//   f0 -> b0 -> b1 -> f1 -> b2 -> b3 -> f2
// Liberty DFFHQx4 / BUFx2 become $dff / $buf so the Yosys test needs no ASAP7.
//
// opt_retime designs in this directory, in the order the pass should learn them:
//   opt_retime_buf.v    $buf chains (this file)                     supported
//   opt_retime_add.v    $add / $sub, the first non-$buf cuts        supported
//   opt_retime_mux.v    $mux, a port that is not an operand         supported
//   opt_retime_cmp.v    comparators and reductions: wide in, one bit out  supported
//   opt_retime_shift.v  variable shifts: fanout and width growth    supported
//                       (a constant shift amount still refuses)
//   opt_retime_acc.v    accumulator / incrementer: the path is a cycle
//
// opt_retime_ops.ys covers the comparators beyond $eq, $xnor, and the rest of
// the $reduce_* family, with designs inline in the script, since they add no
// new rule and only differ in whether the initial state survives the move.
//
// Forward moves only. Backward moves are out of scope: the pass rejects
// -backward while parsing arguments, so do not add designs or tests for them.
//
// Memories, FSMs and multipliers are out of scope: do not add designs for them.
// TODO: revisit after the five categories above pass. $mul is mostly an adder
// tree, so it should follow opt_retime_add.v; memories are not combinational
// cells to move a register across; FSM control cones are a poor early
// correctness target.

module retime_probe (clk, d, q);
  input clk, d;
  output q;
  wire q0, m0, n0, q1, m1, n1;

  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) f0 (.CLK(clk), .D(d),  .Q(q0));
  $buf #(.WIDTH(1))                      b0 (.A(q0),    .Y(m0));
  $buf #(.WIDTH(1))                      b1 (.A(m0),    .Y(n0));
  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) f1 (.CLK(clk), .D(n0), .Q(q1));
  $buf #(.WIDTH(1))                      b2 (.A(q1),    .Y(m1));
  $buf #(.WIDTH(1))                      b3 (.A(m1),    .Y(n1));
  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) f2 (.CLK(clk), .D(n1), .Q(q));
endmodule
