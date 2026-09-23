interface pair_if ();
  logic [3:0] a;
  logic [3:0] b_c;
  modport prod (output a, output b_c);
endinterface

// Registers that are members of an interface port, flattened as `m<modport sep>a`
module producer (input logic clk, input logic [3:0] x, pair_if.prod m);
  always_ff @(posedge clk) begin
    m.a <= x;
    m.b_c <= ~x;
  end
endmodule

// Registers that are members of an interface instance, flattened as `i0<block sep>a`, next to
// an ordinary register whose name only looks like one
module top (input logic clk, input logic [3:0] x, output logic [3:0] y);
  pair_if i0 ();
  pair_if bus ();
  logic [3:0] i0_x;
  always_ff @(posedge clk) begin
    i0.a <= x;
    i0.b_c <= ~x;
    i0_x <= x + 4'd1;
  end
  producer u_p (.clk(clk), .x(x), .m(bus));
  assign y = i0.a ^ i0.b_c ^ i0_x ^ bus.a ^ bus.b_c;
endmodule
