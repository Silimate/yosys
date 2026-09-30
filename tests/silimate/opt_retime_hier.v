// The shared hierarchical fixture: one register with a module boundary on
// either side of it.
//
// Every other opt_retime design in this directory is flat, and
// opt_retime_selection.ys's two modules are siblings that never instantiate
// each other, so nothing here exercised a move whose two ends sit in
// different modules. This design is the smallest one that does.
//
//   top:      a ^ c -> pre
//             u_src (hier_src): pre + b -> mid
//             f1: reg(mid)      -> midq
//             u_dst (hier_dst): ~midq -> out
//
// Read as a timing path it is xor -> add -> reg -> not, and the only moves
// worth making cross a boundary: backward puts the register inside hier_src,
// forward puts it inside hier_dst. The logic on the far side of each boundary
// is a single-input cell so that a move across it clones nothing and the flop
// count is the same before and after, which is what lets a test assert the
// count rather than reason about it.
//
// Both children take clk even though neither uses it. That is the narrow case
// Stage 3 starts from - the destination already has the clock in scope - and
// keeping it in the shared fixture means the clock-availability refusals get
// fixtures of their own rather than being the accidental default here.
//
// midq carries an init so that a move which folds it has somewhere to fold it
// to; sections that do not care set their own.

module hier_src (clk, a, b, y);
  input clk;
  input [7:0] a, b;
  output [7:0] y;

  $add #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    add_s (.A(a), .B(b), .Y(y));
endmodule

module hier_dst (clk, x, z);
  input clk;
  input [7:0] x;
  output [7:0] z;

  $not #(.A_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0)) inv_d (.A(x), .Y(z));
endmodule

module top (clk, a, b, c, out);
  input clk;
  input [7:0] a, b, c;
  output [7:0] out;
  wire [7:0] pre, mid;
  (* init = 8'h00 *) wire [7:0] midq;

  $xor #(.A_WIDTH(8), .B_WIDTH(8), .Y_WIDTH(8), .A_SIGNED(0), .B_SIGNED(0))
    xor_t (.A(a), .B(c), .Y(pre));
  hier_src u_src (.clk(clk), .a(pre), .b(b), .y(mid));
  $dff #(.WIDTH(8), .CLK_POLARITY(1'b1)) f1 (.CLK(clk), .D(mid), .Q(midq));
  hier_dst u_dst (.clk(clk), .x(midq), .z(out));
endmodule
