// Throwaway fixture for retime_debug_all.sh, not a test and not a committed
// design. It exists only because most of the interesting designs live as
// inline heredocs inside the .ys tests, which the debug script cannot read, so
// the gallery had nothing to draw for them. Almost every module here is a copy
// of one in a test; the tests stay the source of truth.
//
// Two groups: the supported moves first, then the designs the pass refuses.
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

// $mul, unsigned full product (from opt_retime_mul.ys). Same merge as $add,
// but Y is the sum of the operand widths, so fa grows from 4 bits to 8.
module fullmul(input clk, input [3:0] a, b, output [7:0] q);
  wire [3:0] ra, rb;
  wire [7:0] y;
  $dff #(.WIDTH(4), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(4), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $mul #(.A_WIDTH(4), .B_WIDTH(4), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    m0 (.A(ra), .B(rb), .Y(y));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(y), .Q(q));
endmodule

// Signed $mul with defined inits (from opt_retime_mul.ys). 4'hf * 4'he is
// 8'h02 signed and 8'hd2 unsigned; the "Folded init" line is 8'h02.
module signedmul(input clk, input [3:0] a, b, output [7:0] q);
  (* init = 4'hf *) wire [3:0] ra;
  (* init = 4'he *) wire [3:0] rb;
  wire [7:0] y;
  $dff #(.WIDTH(4), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(4), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $mul #(.A_WIDTH(4), .B_WIDTH(4), .Y_WIDTH(8), .A_SIGNED(1), .B_SIGNED(1))
    m0 (.A(ra), .B(rb), .Y(y));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(y), .Q(q));
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

// An operand that is half register and half constant (from
// opt_retime_const.ys). A wholly constant operand folds and a wholly
// registered one merges; B here is a concatenation of the two, so each bit
// is classified on its own: the constant nibble stays, fb's low nibble
// merges, and fa resizes onto Y.
module halfconst(input clk, input [7:0] a, b, output [7:0] q);
  wire [7:0] ra, rb, y;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(ra), .B({4'h0, rb[3:0]}), .Y(y));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(y), .Q(q));
endmodule

// Bit-sliced concat on A (from opt_retime_bitslice.ys). Four 2-bit registers
// sharing one enable, plus a wide B. Entering from a slice (f0) or from the
// wide sibling (fb) is the same merge: the named flop resizes to Y and the
// other bit-flops disappear. Give the slices different enables and it stops
// being sound, which is what enmix shows.
module sliced(input clk, en, input [7:0] a, b, output [7:0] q);
  wire [1:0] r0, r1, r2, r3;
  wire [7:0] rb, s;
  $dffe #(.WIDTH(2), .CLK_POLARITY(1'b1), .EN_POLARITY(1'b1))
    f0 (.CLK(clk), .EN(en), .D(a[1:0]), .Q(r0));
  $dffe #(.WIDTH(2), .CLK_POLARITY(1'b1), .EN_POLARITY(1'b1))
    f1 (.CLK(clk), .EN(en), .D(a[3:2]), .Q(r1));
  $dffe #(.WIDTH(2), .CLK_POLARITY(1'b1), .EN_POLARITY(1'b1))
    f2 (.CLK(clk), .EN(en), .D(a[5:4]), .Q(r2));
  $dffe #(.WIDTH(2), .CLK_POLARITY(1'b1), .EN_POLARITY(1'b1))
    f3 (.CLK(clk), .EN(en), .D(a[7:6]), .Q(r3));
  $dffe #(.WIDTH(8), .CLK_POLARITY(1'b1), .EN_POLARITY(1'b1))
    fb (.CLK(clk), .EN(en), .D(b), .Q(rb));
  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A({r3, r2, r1, r0}), .B(rb), .Y(s));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(s), .Q(q));
endmodule

// Signed $sshr with defined inits (from opt_retime_shift.ys). 8'h80 >>> 1 is
// 8'hc0 signed and 8'h40 unsigned; the "Folded init" line is 8'hc0. Pulling
// fq back across s0 is refused: $sshr has no unique inverse.
module signedshift(input clk, input [7:0] a, input [2:0] amt, output [7:0] q);
  (* init = 8'h80 *) wire [7:0] ra;
  (* init = 3'd1 *) wire [2:0] ramt;
  wire [7:0] y;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa   (.CLK(clk), .D(a),   .Q(ra));
  $dff #(.WIDTH(3), .CLK_POLARITY(1'b1)) famt (.CLK(clk), .D(amt), .Q(ramt));
  $sshr #(.A_WIDTH(8), .B_WIDTH(3), .Y_WIDTH(8), .A_SIGNED(1), .B_SIGNED(0))
    s0 (.A(ra), .B(ramt), .Y(y));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fq   (.CLK(clk), .D(y),   .Q(q));
endmodule

// Signed $sshl, widening (from opt_retime_shift.ys). Same merge as shiftwide
// in that test: fa absorbs famt and grows from 8 bits to 11.
module signedleft(input clk, input [7:0] a, input [2:0] amt, output [10:0] q);
  wire [7:0] ra;
  wire [2:0] ramt;
  wire [10:0] sl;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1))  fa   (.CLK(clk), .D(a),   .Q(ra));
  $dff #(.WIDTH(3), .CLK_POLARITY(1'b1))  famt (.CLK(clk), .D(amt), .Q(ramt));
  $sshl #(.A_WIDTH(8), .B_WIDTH(3), .Y_WIDTH(11), .A_SIGNED(1), .B_SIGNED(0))
    s0 (.A(ra), .B(ramt), .Y(sl));
  $dff #(.WIDTH(11), .CLK_POLARITY(1'b1)) fq   (.CLK(clk), .D(sl),  .Q(q));
endmodule

// Backward through a mux tree (from opt_retime_mux_backward.ys). Every level
// has a live select, which is what used to stop the chain after one mux: a
// clone was only allowed at the cut. With clones at every hop, pulling f back
// to u0 crosses u2 as well and leaves five registers, the two on u2 sampling
// s2 and the output of the untouched u1. The select clones both start at 0,
// picking A, which is the port the path runs through at both hops - invisible
// in the pictures, an init being a wire attribute, so read the log lines.
module muxtree(input clk, input [7:0] a, b, c, d, input s0, s1, s2, output [7:0] q);
  (* init = 8'h5a *) wire [7:0] q;
  wire [7:0] m0, m1, m2;
  $mux #(.WIDTH(8)) u0 (.A(a),  .B(b),  .S(s0), .Y(m0));
  $mux #(.WIDTH(8)) u1 (.A(c),  .B(d),  .S(s1), .Y(m1));
  $mux #(.WIDTH(8)) u2 (.A(m0), .B(m1), .S(s2), .Y(m2));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) f (.CLK(clk), .D(m2), .Q(q));
endmodule

// Constant operands (from opt_retime_const.ys). Nothing merges: the constant
// stays wired where it sits, and both registers hop to Y. The incrementer's
// init becomes 8'd1; the mask leaves zero alone.
module constops(input clk, input [7:0] a, b, output [7:0] qinc, qmask);
  wire [7:0] ra, rb, yinc, ymask;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a_inc (.A(ra), .B(8'd1), .Y(yinc));
  $and #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a_mask (.A(rb), .B(8'h0f), .Y(ymask));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fqi (.CLK(clk), .D(yinc),  .Q(qinc));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fqm (.CLK(clk), .D(ymask), .Q(qmask));
endmodule

// $sub, A operand (from opt_retime_sub.ys). Same merge as $add, drawn because
// swapping the operands would still look like a successful move on an $add.
module subdes(input clk, input [7:0] a, b, output [7:0] q);
  wire [7:0] ra, rb, s;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $sub #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    s0 (.A(ra), .B(rb), .Y(s));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(s), .Q(q));
endmodule

// Constant async-load folded through $eq (from opt_retime_reset.ys). fs
// narrows from 3 bits to 1 and async-loads 0, because 3'b000 == 3'b111 is 0.
module aldffeq(input clk, rst_n, input [2:0] d, output eq);
  (* init = 3'h0 *) wire [2:0] q;
  wire y;
  $aldff #(.WIDTH(3), .CLK_POLARITY(1'b1), .ALOAD_POLARITY(1'b0))
    fs (.CLK(clk), .ALOAD(rst_n), .D(d), .AD(3'b000), .Q(q));
  $eq #(.A_WIDTH(3), .B_WIDTH(3), .Y_WIDTH(1), .A_SIGNED(0), .B_SIGNED(0))
    e0 (.A(q), .B(3'b111), .Y(y));
  $aldff #(.WIDTH(1), .CLK_POLARITY(1'b1), .ALOAD_POLARITY(1'b0))
    fq (.CLK(clk), .ALOAD(rst_n), .D(y), .AD(1'b0), .Q(eq));
endmodule

// Backward: $add against a constant (from opt_retime_backward.ys). No clone:
// f(reg(x), c) is reg(f(x, c)), so the flop just hops onto A. Init 0 folds to
// 0xff, which is 0 - 1. unflopped below is the same cell with a live other
// operand, which does clone.
module addc(input clk, input [7:0] a, output [7:0] q);
  (* init = 8'h00 *) wire [7:0] q;
  wire [7:0] y;
  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(a), .B(8'd1), .Y(y));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) f (.CLK(clk), .D(y), .Q(q));
endmodule

// Backward: $not, folding init 0 to 1 (from opt_retime_backward.ys). notpath
// above is the forward direction of the same cell.
module invcap(input clk, input [7:0] a, output [7:0] q);
  (* init = 8'h00 *) wire [7:0] q;
  wire [7:0] y;
  $not #(.A_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0)) n0 (.A(a), .Y(y));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) f (.CLK(clk), .D(y), .Q(q));
endmodule

// Backward: $and against a constant (from opt_retime_and.ys). Same meet as
// addc, but the inverse is not unique: 8'hb0 already sits under the mask, so
// the flop keeps the value it held. andmask in the refused list is this
// design with a stored bit the mask clears.
module andc(input clk, input [7:0] a, output [7:0] q);
  (* init = 8'hb0 *) wire [7:0] q;
  wire [7:0] y;
  $and #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(a), .B(8'hf0), .Y(y));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) f (.CLK(clk), .D(y), .Q(q));
endmodule

// Backward: clone onto a live operand of $and (from opt_retime_and.ys). The
// clone starts at all ones, the identity of the cut, so the named flop keeps
// 8'h5a. 1 register becomes 2.
module andlive(input clk, input [7:0] a, b, output [7:0] q);
  (* init = 8'h5a *) wire [7:0] q;
  wire [7:0] y;
  $and #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(a), .B(b), .Y(y));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) f (.CLK(clk), .D(y), .Q(q));
endmodule

// Backward: $mux, path on A (from opt_retime_mux_backward.ys). Three
// registers: the flop on A, a WIDTH clone on B, and a 1-bit select clone that
// starts at 0 so the mux is A on cycle 0. muxb is the same cell entered on B,
// so that select clone starts at 1 instead.
module muxa(input clk, input [7:0] a, b, input s, output [7:0] q);
  (* init = 8'h5a *) wire [7:0] q;
  wire [7:0] y;
  $mux #(.WIDTH(8)) u0 (.A(a), .B(b), .S(s), .Y(y));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) f (.CLK(clk), .D(y), .Q(q));
endmodule

// Backward: $mux, path on B, A constant (from opt_retime_mux_backward.ys).
// Only the select is cloned, and it starts at 1. 1 register becomes 2, one of
// them a single bit.
module muxb(input clk, input [7:0] b, input s, output [7:0] q);
  (* init = 8'h5a *) wire [7:0] q;
  wire [7:0] y;
  $mux #(.WIDTH(8)) u0 (.A(8'hc3), .B(b), .S(s), .Y(y));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) f (.CLK(clk), .D(y), .Q(q));
endmodule

// Backward: $mux carrying an enable and a sync reset (from
// opt_retime_mux_backward.ys). The clone inherits both, and the select clone
// starts and resets at 0 so a reset cycle still hands the mux the port the
// flop is holding.
module muxrst(input clk, rst, en, input [3:0] a, b, input s, output [3:0] q);
  (* init = 4'h3 *) wire [3:0] q;
  wire [3:0] y;
  $mux #(.WIDTH(4)) u0 (.A(a), .B(b), .S(s), .Y(y));
  $sdffce #(.WIDTH(4), .CLK_POLARITY(1'b1), .EN_POLARITY(1'b1),
            .SRST_POLARITY(1'b1), .SRST_VALUE(4'ha))
    f (.CLK(clk), .EN(en), .SRST(rst), .D(y), .Q(q));
endmodule

// ==========================================================================
// Designs the pass refuses.
//
// These draw as one picture rather than a pair, a refused move having produced
// no after netlist. The galleries run them under REFUSE=1, which is an error
// if the move ever succeeds, so an entry cannot quietly rot into a stale claim
// as the pass grows; it fails and asks to be moved up into the list above.
// ==========================================================================

// An operand that is not registered at all (from opt_retime_add.ys). b arrives
// combinationally, so a forward move of fa across a0 has nothing to merge on B.
// A backward move of fq across a0 is the other direction: that clones fq onto
// A (stacking after fa) and slides fq onto B, proved in opt_retime_backward.ys.
module unflopped(input clk, input [7:0] a, b, output [7:0] q);
  wire [7:0] ra, s;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(ra), .B(b), .Y(s));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(s), .Q(q));
endmodule

// A $mux whose select is live (from opt_retime_mux.ys). The select is an
// operand like any other as far as the move is concerned, so an unregistered
// one blocks it exactly as an unregistered A or B would.
module liveselect(input clk, input [7:0] a, b, input sel, output [7:0] q);
  wire [7:0] ra, rb, m;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $mux #(.WIDTH(8)) m0 (.A(ra), .B(rb), .S(sel), .Y(m));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(m), .Q(q));
endmodule

// A merge candidate that is read somewhere else (from
// opt_retime_merge_fanout.ys). rb feeds the adder and the tap, so fb stays
// and only a0 is rewired to fb's D. The named flop still moves.
module tapped(input clk, input [7:0] a, b, output [7:0] q, tap);
  wire [7:0] ra, rb, s;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(ra), .B(rb), .Y(s));
  $buf #(.WIDTH(8)) bt (.A(rb), .Y(tap));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(s), .Q(q));
endmodule

// Enables that disagree (from opt_retime_enable.ys). Both registers are $dffe
// on the same net, but the polarities are opposite, so one holds while the
// other loads. That feeds the adder a mix of old and new operands, and the
// single register left behind has no way to reproduce it. Note EN_POLARITY is
// a parameter rather than part of the type, so the two cells draw identically
// and the pictures cannot show the difference at all.
module enmix(input clk, en, input [7:0] a, b, output [7:0] q);
  wire [7:0] ra, rb, s;
  $dffe #(.WIDTH(8), .CLK_POLARITY(1'b1), .EN_POLARITY(1'b1))
    fa (.CLK(clk), .EN(en), .D(a), .Q(ra));
  $dffe #(.WIDTH(8), .CLK_POLARITY(1'b1), .EN_POLARITY(1'b0))
    fb (.CLK(clk), .EN(en), .D(b), .Q(rb));
  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(ra), .B(rb), .Y(s));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(s), .Q(q));
endmodule

// Resets on different nets (from opt_retime_reset.ys). The values 8'h03 and
// 8'h04 would fold together happily, which rstfold above does; what cannot be
// folded is one register resetting while the other does not, for the same
// reason enmix cannot. The two reset nets are visible in the pictures here,
// unlike the polarity in enmix.
module rstmix(input clk, rst, rst2, input [7:0] a, b, output [7:0] q);
  wire [7:0] ra, rb, s;
  $sdff #(.WIDTH(8), .CLK_POLARITY(1'b1), .SRST_POLARITY(1'b1), .SRST_VALUE(8'h03))
    fa (.CLK(clk), .SRST(rst), .D(a), .Q(ra));
  $sdff #(.WIDTH(8), .CLK_POLARITY(1'b1), .SRST_POLARITY(1'b1), .SRST_VALUE(8'h04))
    fb (.CLK(clk), .SRST(rst2), .D(b), .Q(rb));
  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(ra), .B(rb), .Y(s));
  $sdff #(.WIDTH(8), .CLK_POLARITY(1'b1), .SRST_POLARITY(1'b1), .SRST_VALUE(8'h00))
    fq (.CLK(clk), .SRST(rst), .D(s), .Q(q));
endmodule

// One init value defined and one not (from opt_retime_cmp.ys). Folding 8'h0f
// against an undefined value gives undefined bits back, which would throw away
// what the defined side said, so the move is refused rather than folded. Both
// registers having an init, or neither, would be fine.
module mixinit(input clk, input [7:0] a, b, output [7:0] q);
  (* init = 8'h0f *) wire [7:0] ra;
  wire [7:0] rb, s;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(ra), .B(rb), .Y(s));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(s), .Q(q));
endmodule

// A single-bit register that would have to widen (from opt_retime_width.ys).
// The $add keeps its carry, so the survivor needs 2 bits, and $_DFF_P_ has no
// width parameter to grow. carryout at the top of this file is the same move
// on a coarse register, where it simply resizes.
module fine(input clk, input a, b, output [1:0] q);
  wire ra, rb;
  wire [1:0] s;
  $_DFF_P_ fa (.C(clk), .D(a), .Q(ra));
  $_DFF_P_ fb (.C(clk), .D(b), .Q(rb));
  $add #(.A_WIDTH(1), .B_WIDTH(1), .Y_WIDTH(2), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(ra), .B(rb), .Y(s));
  $dff #(.WIDTH(2), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(s), .Q(q));
endmodule

// Backward: a width change (from opt_retime_backward.ys). The $add keeps its
// carry, so Y is 9 bits and the live operand is 8. Forward across this shape
// resizes (carryout above); backward cannot invert it yet.
module backwide(input clk, input [7:0] a, output [8:0] q);
  wire [8:0] y;
  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(9), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(a), .B(8'd1), .Y(y));
  $dff #(.WIDTH(9), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(y), .Q(q));
endmodule

// Backward: the path would land on a $mux select (from
// opt_retime_mux_backward.ys). Both data ports are constant, so the select is
// the only live input left to slide onto - and it is the one operand that
// cannot be the path, being the clone that pays for cycle 0. With the select
// gone, the clones on A and B would each have to start at the stored value
// rather than at a fixed identity.
module selpath(input clk, input s, output [7:0] q);
  wire [7:0] y;
  $mux #(.WIDTH(8)) u0 (.A(8'haa), .B(8'h55), .S(s), .Y(y));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) f (.CLK(clk), .D(y), .Q(q));
endmodule

// Backward: the cut Y has another reader (from opt_retime_merge_fanout.ys).
// Forward can leave a leftover copy for extra readers of Q; backward needs
// Y to drive only the flop being moved. bt is the extra reader.
module backfanout(input clk, input [7:0] a, output [7:0] q, tap);
  wire [7:0] y;
  $buf #(.WIDTH(8)) b0 (.A(a), .Y(y));
  $buf #(.WIDTH(8)) bt (.A(y), .Y(tap));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(y), .Q(q));
endmodule

// Backward: a stored bit the mask clears (from opt_retime_and.ys). Same $and
// as andc above, but 8'h0f asks for bits 8'hf0 zeros, so no input produces
// the stored value and there is nothing to leave the flop holding.
module andmask(input clk, input [7:0] a, output [7:0] q);
  (* init = 8'h0f *) wire [7:0] q;
  wire [7:0] y;
  $and #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(a), .B(8'hf0), .Y(y));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) f (.CLK(clk), .D(y), .Q(q));
endmodule

// Backward: every data input is constant (from opt_retime_const.ys). There is
// no live port to slide onto, constants needing no register.
module allconst(input clk, output [7:0] q);
  wire [7:0] y;
  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(8'd1), .B(8'd2), .Y(y));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) f (.CLK(clk), .D(y), .Q(q));
endmodule

// A cut type that is not on the forward allowlist (from opt_retime_mul.ys).
// $div is a pure function of two operands the same way $mul is; it is left
// out until something tests it. $mul is fullmul above.
module divcut(input clk, input [7:0] a, b, output [7:0] q);
  wire [7:0] ra, rb, y;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $div #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    d0 (.A(ra), .B(rb), .Y(y));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(y), .Q(q));
endmodule

// An async load arriving on a net (from opt_retime_init.ys). A constant AD
// folds, which is aldffeq above; a net has nothing to evaluate, so the move
// cannot push the load through n0.
module aloadnet(input clk, aload, input [7:0] a, ad, output [7:0] q);
  wire [7:0] ra, y;
  $aldff #(.WIDTH(8), .CLK_POLARITY(1'b1), .ALOAD_POLARITY(1'b1))
    fa (.CLK(clk), .ALOAD(aload), .AD(ad), .D(a), .Q(ra));
  $not #(.A_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0)) n0 (.A(ra), .Y(y));
  $aldff #(.WIDTH(8), .CLK_POLARITY(1'b1), .ALOAD_POLARITY(1'b1))
    fq (.CLK(clk), .ALOAD(aload), .AD(8'h00), .D(y), .Q(q));
endmodule
