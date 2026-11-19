module m #(parameter logic [8191:0] P = '0) (input logic [7:0] a, output logic [7:0] y);
  assign y = a ^ P[7:0] ^ P[8191:8184];
endmodule

module top (input logic [7:0] a, output logic [7:0] y0, y1, y2);
  m #(.P({256{32'hdeadbeef}})) u0 (.a, .y(y0));
  m #(.P({256{32'hcafef00d}})) u1 (.a, .y(y1));
  m #(.P(1)) u2 (.a, .y(y2));
endmodule
