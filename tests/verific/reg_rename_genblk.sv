// Synthetic repro for reg_rename unplaced shapes seen on a customer power run.

// Unpacked-array shift register: element 0 is the input, 1..DEPTH are flops.
module shift_pipe #(parameter W = 4, parameter DEPTH = 3) (
  input  logic         clk,
  input  logic         rst_n,
  input  logic [W-1:0] din,
  output logic [W-1:0] dout
);
  logic [W-1:0] data_pipes_reg [0:DEPTH];
  assign data_pipes_reg[0] = din;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      for (int i = 1; i <= DEPTH; i++) data_pipes_reg[i] <= '0;
    end else begin
      for (int i = 1; i <= DEPTH; i++) data_pipes_reg[i] <= data_pipes_reg[i-1];
    end
  end
  assign dout = data_pipes_reg[DEPTH];
endmodule

// Registers inside a named generate-if block.
module cal #(parameter HW = 1) (
  input  logic       clk,
  input  logic       rst_n,
  input  logic [7:0] din,
  output logic [7:0] dout
);
  if (HW) begin : hw_gen
    logic [7:0] thr_p1;
    logic [3:0] cnt;
    always_ff @(posedge clk or negedge rst_n) begin
      if (!rst_n) begin
        thr_p1 <= '0;
        cnt <= '0;
      end else begin
        thr_p1 <= din;
        cnt <= cnt + 4'd1;
      end
    end
    assign dout = thr_p1 ^ {cnt, cnt};
  end else begin : sw_gen
    assign dout = din;
  end
endmodule

module top (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [7:0]  din,
  output logic [15:0] dout,
  output logic [3:0]  sq
);
  for (genvar g = 0; g < 2; g++) begin : gen_dp
    cal #(.HW(1)) u_cal (.clk(clk), .rst_n(rst_n), .din(din ^ 8'(g)), .dout(dout[g*8 +: 8]));
  end
  shift_pipe #(.W(4), .DEPTH(3)) u_pipe (.clk(clk), .rst_n(rst_n), .din(din[3:0]), .dout(sq));
endmodule
