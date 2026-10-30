typedef struct packed {
  logic [3:0] a;
  logic       b;
} ab_t;

module top (input ab_t d);
  ab_t s;
  ab_t [1:0] pa;
  ab_t ua [0:1];
  logic [1:0][2:0] md [0:1];
  assign s = d;
  assign pa = {d, ~d};
  assign ua = '{d, ~d};
  assign md = '{{d, 1'b0}, {~d, 1'b1}};
endmodule

// A register anchored at an element of mem
module regs (input logic clk, input logic [3:0] d);
  logic [3:0] mem [0:7];
  always_ff @(posedge clk)
    mem[3] <= d;
endmodule
