// A window read whose wrap depends on a live mode bit: `seg = DEPTH >> mode`
// makes both the modulo divisor and the bank offset variable, and `ptr * step`
// is var*var, so the index is not affine and the uniform-gather fold gives up.
// Each lane's index is still a function of only {mode, ptr} -- 3 bits -- so it
// reaches at most 8 of the 32 entries.
module opt_vps_small_support #(
  parameter DEPTH = 32,
  parameter LANES = 8,
  parameter W     = 4
) (
  input                         clk,
  input                         mode,
  input      [DEPTH-1:0][W-1:0] din,
  output reg [LANES-1:0][W-1:0] y
);
  reg [DEPTH-1:0][W-1:0] mem;
  reg [1:0]              ptr;

  wire [6:0] seg  = DEPTH >> mode;
  wire [4:0] step = (DEPTH / 4) >> mode;

  always @(posedge clk) begin
    mem <= din;
    ptr <= ptr + 2'd1;
  end

  for (genvar i = 0; i < LANES; i++) begin : g
    wire [6:0] bank = (i >> (clogb2(LANES) - mode)) & 1;
    always @(posedge clk)
      y[i] <= mem[((ptr * step + i) % seg) + bank * seg];
  end

  function automatic integer clogb2(input integer depth);
    integer k;
    begin
      k = depth - 1;
      for (clogb2 = 0; k > 0; clogb2 = clogb2 + 1)
        k = k >> 1;
    end
  endfunction
endmodule

// The same 8-lane window over a 32-entry buffer at two pointer strides, to pin the
// gather fold's cost check in both directions. Both indices are affine in a 2-bit
// pointer, so both groups fold to a barrel without -read-support.
//
// stride 8: the barrel shifts by `ptr * 8`, a 5-bit amount of which two bits vary, and
// keeps two levels as wide as its 32-entry source -- 64 muxes per element bit against
// 8 lanes x 3 for four-entry reads. Left as narrow reads.
module opt_vps_small_support_stride #(
  parameter DEPTH  = 32,
  parameter LANES  = 8,
  parameter STRIDE = 8,
  parameter W      = 4
) (
  input                         clk,
  input      [DEPTH-1:0][W-1:0] din,
  output reg [LANES-1:0][W-1:0] y
);
  reg [DEPTH-1:0][W-1:0] mem;
  reg [1:0]              ptr;

  always @(posedge clk) begin
    mem <= din;
    ptr <= ptr + 2'd1;
  end

  for (genvar i = 0; i < LANES; i++) begin : g
    wire [4:0] idx = ptr * STRIDE + i;
    always @(posedge clk)
      y[i] <= mem[idx];
  end
endmodule
