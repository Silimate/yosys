// Throwaway fixture for retime_debug_all.sh, not a test and not a committed
// design. It exists only because some supported moves live as inline heredocs
// inside the .ys tests, which the debug script cannot read, so the gallery had
// no before/after for them. Every module here is a copy of one in a test; the
// tests stay the source of truth.
//
// Delete this alongside the retime_debug*.sh scripts.

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

// $ne, $lt, $gt and the rest of the $reduce_* family (from opt_retime_ops.ys).
// All of these give zero on the all-zero state, hence the name. The three
// comparators merge their second operand away, the three reductions have
// nothing to merge, and every survivor narrows from 8 bits to 1.
module zeroinit(input clk, input [7:0] a, b, c, d, e, g, h, i, j,
                output qne, qlt, qgt, qand, qxor, qbool);
  wire [7:0] ra, rb, rc, rd, re, rg, rh, ri, rj;
  wire yne, ylt, ygt, yand, yxor, ybool;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fc (.CLK(clk), .D(c), .Q(rc));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fd (.CLK(clk), .D(d), .Q(rd));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fe (.CLK(clk), .D(e), .Q(re));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fg (.CLK(clk), .D(g), .Q(rg));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fh (.CLK(clk), .D(h), .Q(rh));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fi (.CLK(clk), .D(i), .Q(ri));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fj (.CLK(clk), .D(j), .Q(rj));
  $ne #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(1), .A_SIGNED(0), .B_SIGNED(0))
    c_ne (.A(ra), .B(rb), .Y(yne));
  $lt #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(1), .A_SIGNED(0), .B_SIGNED(0))
    c_lt (.A(rc), .B(rd), .Y(ylt));
  $gt #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(1), .A_SIGNED(0), .B_SIGNED(0))
    c_gt (.A(ri), .B(rj), .Y(ygt));
  $reduce_and #(.A_WIDTH(8), .Y_WIDTH(1), .A_SIGNED(0)) r_and (.A(re), .Y(yand));
  $reduce_xor #(.A_WIDTH(8), .Y_WIDTH(1), .A_SIGNED(0)) r_xor (.A(rg), .Y(yxor));
  $reduce_bool #(.A_WIDTH(8), .Y_WIDTH(1), .A_SIGNED(0)) r_bool (.A(rh), .Y(ybool));
  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) fqne   (.CLK(clk), .D(yne),   .Q(qne));
  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) fqlt   (.CLK(clk), .D(ylt),   .Q(qlt));
  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) fqgt   (.CLK(clk), .D(ygt),   .Q(qgt));
  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) fqand  (.CLK(clk), .D(yand),  .Q(qand));
  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) fqxor  (.CLK(clk), .D(yxor),  .Q(qxor));
  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) fqbool (.CLK(clk), .D(ybool), .Q(qbool));
endmodule

// $xnor, $reduce_xnor, $le and $ge (from opt_retime_ops.ys). None of these
// produce zero from the all-zero state, so the retimed design only matches the
// original if the initial state is mapped through the cell; that test maps it,
// this fixture is only here for the picture.
module onesinit(input clk, input [7:0] a, b, c, d, e, g, h,
                output [7:0] qx, output qr, qle, qge);
  wire [7:0] ra, rb, rc, rd, re, rg, rh, yx;
  wire yr, yle, yge;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fc (.CLK(clk), .D(c), .Q(rc));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fd (.CLK(clk), .D(d), .Q(rd));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fe (.CLK(clk), .D(e), .Q(re));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fg (.CLK(clk), .D(g), .Q(rg));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fh (.CLK(clk), .D(h), .Q(rh));
  $xnor #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    c_xnor (.A(ra), .B(rb), .Y(yx));
  $reduce_xnor #(.A_WIDTH(8), .Y_WIDTH(1), .A_SIGNED(0)) r_xnor (.A(rc), .Y(yr));
  $le #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(1), .A_SIGNED(0), .B_SIGNED(0))
    c_le (.A(rd), .B(re), .Y(yle));
  $ge #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(1), .A_SIGNED(0), .B_SIGNED(0))
    c_ge (.A(rg), .B(rh), .Y(yge));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fqx  (.CLK(clk), .D(yx),  .Q(qx));
  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) fqr  (.CLK(clk), .D(yr),  .Q(qr));
  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) fqle (.CLK(clk), .D(yle), .Q(qle));
  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) fqge (.CLK(clk), .D(yge), .Q(qge));
endmodule

// Clock enables (from opt_retime_enable.ys). The enable travels with the
// register rather than being folded, so the thing to look for in the picture
// is the EN port surviving on fa and fc while the registers merged into them
// take theirs away with them. 7 registers become 4.
module enops(input clk, en, input [7:0] a, b, c, d, input s_in,
             output [7:0] qadd, qmux);
  wire [7:0] ra, rb, rc, rd, sum, mx;
  wire rs;
  $dffe #(.WIDTH(8), .CLK_POLARITY(1'b1), .EN_POLARITY(1'b1))
    fa (.CLK(clk), .EN(en), .D(a), .Q(ra));
  $dffe #(.WIDTH(8), .CLK_POLARITY(1'b1), .EN_POLARITY(1'b1))
    fb (.CLK(clk), .EN(en), .D(b), .Q(rb));
  $dffe #(.WIDTH(8), .CLK_POLARITY(1'b1), .EN_POLARITY(1'b1))
    fc (.CLK(clk), .EN(en), .D(c), .Q(rc));
  $dffe #(.WIDTH(8), .CLK_POLARITY(1'b1), .EN_POLARITY(1'b1))
    fd (.CLK(clk), .EN(en), .D(d), .Q(rd));
  $dffe #(.WIDTH(1), .CLK_POLARITY(1'b1), .EN_POLARITY(1'b1))
    fs (.CLK(clk), .EN(en), .D(s_in), .Q(rs));
  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(ra), .B(rb), .Y(sum));
  $mux #(.WIDTH(8)) m0 (.A(rc), .B(rd), .S(rs), .Y(mx));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fqa (.CLK(clk), .D(sum), .Q(qadd));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fqm (.CLK(clk), .D(mx),  .Q(qmux));
endmodule

// Init values folded and relocated (from opt_retime_init.ys). Nothing about
// this is visible in either rendering, because an init value is a wire
// attribute rather than a port: read the "Folded init value" lines above the
// pictures instead. The $buf pair is the case that needs no arithmetic and
// still needs the value moved onto the register's new Q net, which was
// silently wrong before folding existed. 9 registers become 6.
module initmerge(input clk, input [7:0] a, b, c, d, e, input s_in,
                 output [7:0] qbuf, qadd, qmux);
  (* init = 8'h5a *) wire [7:0] rbuf;
  (* init = 8'h03 *) wire [7:0] ra;
  (* init = 8'h04 *) wire [7:0] rb;
  (* init = 8'haa *) wire [7:0] rc;
  (* init = 8'h55 *) wire [7:0] rd;
  (* init = 1'b1  *) wire rs;
  wire [7:0] mid, tail, sum, mx;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fbuf (.CLK(clk), .D(e), .Q(rbuf));
  $buf #(.WIDTH(8)) b0 (.A(rbuf), .Y(mid));
  $buf #(.WIDTH(8)) b1 (.A(mid),  .Y(tail));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fqb (.CLK(clk), .D(tail), .Q(qbuf));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(ra), .B(rb), .Y(sum));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fqa (.CLK(clk), .D(sum), .Q(qadd));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fc (.CLK(clk), .D(c), .Q(rc));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fd (.CLK(clk), .D(d), .Q(rd));
  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) fs (.CLK(clk), .D(s_in), .Q(rs));
  $mux #(.WIDTH(8)) mm (.A(rc), .B(rd), .S(rs), .Y(mx));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fqm (.CLK(clk), .D(mx), .Q(qmux));
endmodule

// A folded init value that also changes width (from opt_retime_init.ys). The
// reduction narrows its register from 8 bits to 1 and |8'h0f narrows with it;
// the $add keeps its carry so the other widens to 9 and 8'hff + 8'h01 lands on
// the bit a fold done at the old width would have dropped. The graphviz view
// is where those width changes show up. 5 registers become 4.
module initresize(input clk, input [7:0] a, b, c, output qred, output [8:0] qcar);
  (* init = 8'h0f *) wire [7:0] rr;
  (* init = 8'hff *) wire [7:0] rca;
  (* init = 8'h01 *) wire [7:0] rcb;
  wire red;
  wire [8:0] car;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fr (.CLK(clk), .D(a), .Q(rr));
  $reduce_or #(.A_WIDTH(8), .Y_WIDTH(1), .A_SIGNED(0)) r0 (.A(rr), .Y(red));
  $dff #(.WIDTH(1), .CLK_POLARITY(1'b1)) fqr (.CLK(clk), .D(red), .Q(qred));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fca (.CLK(clk), .D(b), .Q(rca));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fcb (.CLK(clk), .D(c), .Q(rcb));
  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(9), .A_SIGNED(0), .B_SIGNED(0))
    c0 (.A(rca), .B(rcb), .Y(car));
  $dff #(.WIDTH(9), .CLK_POLARITY(1'b1)) fqc (.CLK(clk), .D(car), .Q(qcar));
endmodule

// Sync reset values folded (from opt_retime_reset.ys). The SRST port stays put
// while the value it loads is recomputed, so again the "Folded sync reset
// value" lines carry the information the pictures cannot. fa and fb reset to
// 8'h03 and 8'h04 on one net and merge into a single register resetting to
// 8'h07, which is the case where merged registers are allowed to disagree.
// 5 registers become 4.
module rstfold(input clk, rst, input [7:0] a, b, c, output [7:0] qn, qs);
  (* init = 8'h00 *) wire [7:0] rn;
  (* init = 8'h03 *) wire [7:0] ra;
  (* init = 8'h04 *) wire [7:0] rb;
  wire [7:0] n, s;
  $sdff #(.WIDTH(8), .CLK_POLARITY(1'b1), .SRST_POLARITY(1'b1), .SRST_VALUE(8'h00))
    fn (.CLK(clk), .SRST(rst), .D(a), .Q(rn));
  $not #(.A_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0)) n0 (.A(rn), .Y(n));
  $sdff #(.WIDTH(8), .CLK_POLARITY(1'b1), .SRST_POLARITY(1'b1), .SRST_VALUE(8'h00))
    fqn (.CLK(clk), .SRST(rst), .D(n), .Q(qn));
  $sdff #(.WIDTH(8), .CLK_POLARITY(1'b1), .SRST_POLARITY(1'b1), .SRST_VALUE(8'h03))
    fa (.CLK(clk), .SRST(rst), .D(b), .Q(ra));
  $sdff #(.WIDTH(8), .CLK_POLARITY(1'b1), .SRST_POLARITY(1'b1), .SRST_VALUE(8'h04))
    fb (.CLK(clk), .SRST(rst), .D(c), .Q(rb));
  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(ra), .B(rb), .Y(s));
  $sdff #(.WIDTH(8), .CLK_POLARITY(1'b1), .SRST_POLARITY(1'b1), .SRST_VALUE(8'h00))
    fqs (.CLK(clk), .SRST(rst), .D(s), .Q(qs));
endmodule

// The one folded value that is visible in the rendering (from
// opt_retime_reset.ys). A single-bit cell spells the value it resets to into
// its type name, so folding 0 to 1 across the $not turns $_SDFF_PP0_ into
// $_SDFF_PP1_ and the box label changes. fq is untouched and stays PP0.
// The register count does not move: nothing merges and the width is unchanged.
module finerst(input clk, rst, d, output q);
  (* init = 1'b0 *) wire r0;
  wire n;
  $_SDFF_PP0_ ff (.C(clk), .R(rst), .D(d), .Q(r0));
  $not #(.A_WIDTH(1), .Y_WIDTH(1), .A_SIGNED(0)) n0 (.A(r0), .Y(n));
  $_SDFF_PP0_ fq (.C(clk), .R(rst), .D(n), .Q(q));
endmodule

// An async reset value folded through a merge (from opt_retime_reset.ys).
// Identical to the sync case except for when the register loads the value:
// 8'h0a | 8'h05 is 8'h0f. 3 registers become 2.
module arstfold(input clk, rst, input [7:0] a, b, output [7:0] q);
  (* init = 8'h0a *) wire [7:0] ra;
  (* init = 8'h05 *) wire [7:0] rb;
  wire [7:0] s;
  $adff #(.WIDTH(8), .CLK_POLARITY(1'b1), .ARST_POLARITY(1'b1), .ARST_VALUE(8'h0a))
    fa (.CLK(clk), .ARST(rst), .D(a), .Q(ra));
  $adff #(.WIDTH(8), .CLK_POLARITY(1'b1), .ARST_POLARITY(1'b1), .ARST_VALUE(8'h05))
    fb (.CLK(clk), .ARST(rst), .D(b), .Q(rb));
  $or #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    o0 (.A(ra), .B(rb), .Y(s));
  $adff #(.WIDTH(8), .CLK_POLARITY(1'b1), .ARST_POLARITY(1'b1), .ARST_VALUE(8'h0f))
    fq (.CLK(clk), .ARST(rst), .D(s), .Q(q));
endmodule
