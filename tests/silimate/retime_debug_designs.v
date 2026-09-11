// Throwaway fixture for retime_debug_all.sh, not a test and not a committed
// design. It exists only because some supported moves live as inline heredocs
// inside the .ys tests, which the debug script cannot read, so the gallery had
// no before/after for them. Every module here is a copy of one in a test; the
// tests stay the source of truth.
//
// Delete this alongside retime_debug.sh and retime_debug_all.sh.

// Widening: the $add keeps its carry, so a forward move across a0 resizes fa
// from 8 to 9 bits. 3 registers and 25 bits become 2 and 18.
module carryout(input clk, input [7:0] a, b, output [8:0] q);
  wire [7:0] ra, rb;
  wire [8:0] s;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(9), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(ra), .B(rb), .Y(s));
  $dff #(.WIDTH(9), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(s), .Q(q));
endmodule

// Narrowing: the $add truncates, so the same move resizes fa from 8 to 4 bits.
// 3 registers and 20 bits become 2 and 8.
module narrow(input clk, input [7:0] a, b, output [3:0] q);
  wire [7:0] ra, rb;
  wire [3:0] s;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(4), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(ra), .B(rb), .Y(s));
  $dff #(.WIDTH(4), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(s), .Q(q));
endmodule

// $or and $xor, two independent cones (from opt_retime_cmp.ys). Each move
// merges its other operand away: 6 registers become 4.
module bitwise(input clk, input [7:0] a, b, c, d, output [7:0] qo, qx);
  wire [7:0] ra, rb, rc, rd, o, x;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fc (.CLK(clk), .D(c), .Q(rc));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fd (.CLK(clk), .D(d), .Q(rd));
  $or #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    o0 (.A(ra), .B(rb), .Y(o));
  $xor #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    x0 (.A(rc), .B(rd), .Y(x));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fqo (.CLK(clk), .D(o), .Q(qo));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fqx (.CLK(clk), .D(x), .Q(qx));
endmodule

// $not: merges nothing and preserves width, so the register simply hops the
// cell and the register count does not change. Note this is the one supported
// cut where f(0) is not 0, so the retimed design only matches the original if
// the initial state is mapped through the $not; opt_retime_cmp.ys does that.
module notpath(input clk, input [7:0] a, output [7:0] q);
  wire [7:0] ra, n;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $not #(.A_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0)) n0 (.A(ra), .Y(n));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(n), .Q(q));
endmodule

// $ne, $lt and the rest of the $reduce_* family (from opt_retime_ops.ys). The
// two comparators merge their second operand away, the three reductions have
// nothing to merge, and every survivor narrows from 8 bits to 1.
module siblings(input clk, input [7:0] a, b, c, d, e, g, h,
                output qne, qlt, qand, qxor, qbool);
  wire [7:0] ra, rb, rc, rd, re, rg, rh;
  wire yne, ylt, yand, yxor, ybool;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fc (.CLK(clk), .D(c), .Q(rc));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fd (.CLK(clk), .D(d), .Q(rd));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fe (.CLK(clk), .D(e), .Q(re));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fg (.CLK(clk), .D(g), .Q(rg));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fh (.CLK(clk), .D(h), .Q(rh));
  $ne #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(1), .A_SIGNED(0), .B_SIGNED(0))
    c_ne (.A(ra), .B(rb), .Y(yne));
  $lt #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(1), .A_SIGNED(0), .B_SIGNED(0))
    c_lt (.A(rc), .B(rd), .Y(ylt));
  $reduce_and #(.A_WIDTH(8), .Y_WIDTH(1), .A_SIGNED(0)) r_and (.A(re), .Y(yand));
  $reduce_xor #(.A_WIDTH(8), .Y_WIDTH(1), .A_SIGNED(0)) r_xor (.A(rg), .Y(yxor));
  $reduce_bool #(.A_WIDTH(8), .Y_WIDTH(1), .A_SIGNED(0)) r_bool (.A(rh), .Y(ybool));
  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) fqne   (.CLK(clk), .D(yne),   .Q(qne));
  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) fqlt   (.CLK(clk), .D(ylt),   .Q(qlt));
  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) fqand  (.CLK(clk), .D(yand),  .Q(qand));
  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) fqxor  (.CLK(clk), .D(yxor),  .Q(qxor));
  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) fqbool (.CLK(clk), .D(ybool), .Q(qbool));
endmodule

// $xnor and $reduce_xnor (from opt_retime_ops.ys). Both invert, so the retimed
// design only matches the original if the initial state is inverted with it;
// that test maps it, this fixture is only here for the picture.
module inverting(input clk, input [7:0] a, b, c, output [7:0] qx, output qr);
  wire [7:0] ra, rb, rc, yx;
  wire yr;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fc (.CLK(clk), .D(c), .Q(rc));
  $xnor #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    c_xnor (.A(ra), .B(rb), .Y(yx));
  $reduce_xnor #(.A_WIDTH(8), .Y_WIDTH(1), .A_SIGNED(0)) r_xnor (.A(rc), .Y(yr));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fqx (.CLK(clk), .D(yx), .Q(qx));
  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) fqr (.CLK(clk), .D(yr), .Q(qr));
endmodule
