module top (
  input  logic       clk,
  input  logic [3:0] d,
  output logic [3:0] y
);
  logic [3:0] a;
  logic [0:3] b;
  logic [5:2] c;
  logic [1:0] m [0:1];
  always_ff @(posedge clk) begin
    a <= d;
    b <= ~d;
    c <= d + 4'd1;
    m[0] <= d[1:0];
    m[1] <= d[3:2];
  end
  assign y = a ^ b ^ c ^ {m[1], m[0]};
endmodule
