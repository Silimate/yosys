// Same topology as preqorsor tests/unit/eda/test_retime_candidates.py:
//   f0 -> b0 -> b1 -> f1 -> b2 -> b3 -> f2
// Liberty DFFHQx4 / BUFx2 become $dff / $buf so the Yosys test needs no ASAP7.

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
