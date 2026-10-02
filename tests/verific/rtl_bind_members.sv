typedef struct packed {
  logic [1:0] p;
  logic       q;
} pq_t;

typedef struct packed {
  logic [3:0] a;
  struct packed {
    logic [1:0] p;
    logic       q;
  } n;
  pq_t  [1:0] pa;
  logic b;
} s_t;

interface bus_if();
  logic [7:0] data;
  logic [1:0] mask;
  modport tx (output data, output mask);
endinterface

module top (
  input  logic       clk,
  input  s_t         d,
  input  logic [9:0] e,
  output s_t         y,
  output s_t         z,
  output logic [9:0] w
);
  s_t s;
  s_t arr [0:1];
  bus_if bus_q();
  always_ff @(posedge clk) begin
    s <= d;
    arr[0] <= d;
    arr[1] <= ~d;
    bus_q.data <= e[9:2];
    bus_q.mask <= e[1:0];
  end
  assign y = s;
  assign z = arr[0] ^ arr[1];
  assign w = {bus_q.data, bus_q.mask};
endmodule
