module activity_edge (input clk, input flip, input quiet, input [1:0] bus, input xz, output reg y);
  always @(posedge clk) y <= flip ^ quiet ^ bus[0] ^ bus[1] ^ xz;
endmodule
