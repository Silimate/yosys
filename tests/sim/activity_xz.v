module activity_xz (input clk, input held, input gated, input dark, output reg y);
  always @(posedge clk) y <= (held & gated) | dark;
endmodule
