// Throwaway fixture for retime_debug_all.sh, not a test and not a committed
// design. It exists only because most of the interesting designs live as
// inline heredocs inside the .ys tests, which the debug script cannot read, so
// the gallery had nothing to draw for them. Almost every module here is a copy
// of one in a test; the tests stay the source of truth.
//
// Two groups: the supported moves first, then the designs the pass refuses.
// The one module with no test behind it is sliced, at the end, which is a move
// that ought to work rather than one that should not.
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

// ==========================================================================
// Designs the pass refuses.
//
// These draw as one picture rather than a pair, a refused move having produced
// no after netlist. The galleries run them under REFUSE=1, which is an error
// if the move ever succeeds, so an entry cannot quietly rot into a stale claim
// as the pass grows; it fails and asks to be moved up into the list above.
// ==========================================================================

// An operand that is not registered at all (from opt_retime_add.ys). b arrives
// combinationally, so input B has no register to merge and the move would have
// to invent one. The most basic thing a forward move needs.
module unflopped(input clk, input [7:0] a, b, output [7:0] q);
  wire [7:0] ra, s;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(ra), .B(b), .Y(s));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(s), .Q(q));
endmodule

// An operand that is half register and half constant (from
// opt_retime_const.ys). A wholly constant operand folds and a wholly
// registered one merges, but B here is a concatenation of the two, so it is
// neither: a register feeds only part of the port. The picture is worth
// reading next to sliced at the bottom, which fails the same check.
module halfconst(input clk, input [7:0] a, b, output [7:0] q);
  wire [7:0] ra, rb, y;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa (.CLK(clk), .D(a), .Q(ra));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fb (.CLK(clk), .D(b), .Q(rb));
  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    a0 (.A(ra), .B({4'h0, rb[3:0]}), .Y(y));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fq (.CLK(clk), .D(y), .Q(q));
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

// A cut the pass has no rule for (from opt_retime_shift.ys). $sshr is a pure
// function of its operands like every supported cut, so the move is sound; it
// is simply not on the list, since a signed shift needs the sign handled when
// folding stored values. A refusal by omission rather than by principle.
module signedshift(input clk, input [7:0] a, input [2:0] amt, output [7:0] q);
  wire [7:0] ra, y;
  wire [2:0] ramt;
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fa   (.CLK(clk), .D(a),   .Q(ra));
  $dff #(.WIDTH(3), .CLK_POLARITY(1'b1)) famt (.CLK(clk), .D(amt), .Q(ramt));
  $sshr #(.A_WIDTH(8), .B_WIDTH(3), .Y_WIDTH(8), .A_SIGNED(1), .B_SIGNED(0))
    s0 (.A(ra), .B(ramt), .Y(y));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) fq   (.CLK(clk), .D(y),   .Q(q));
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

// The odd one out: a refusal that is a gap rather than a boundary, and the one
// module here with no .ys test behind it.
//
// Input A is four 2-bit registers concatenated, bit-sliced datapath style, all
// sharing one enable. It trips the same check as halfconst, no single driver
// for the whole port, and it also cannot be entered from a slice, since the
// chain walk only follows a port carrying the whole signal. But unlike every
// other design in this section the move is sound: with one shared enable the
// slices are all the same age, so the concatenation behaves as one register
// and hand-building the retimed form proves equivalent. Give the slices
// different enables and it stops being sound, which is what enmix shows.
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
