// Uniform scatter: L lanes written at a variable base with a fixed stride, the
// idiom Verific lowers to one one-hot decoder per lane plus an N-wide stage of
// element muxes per lane -- N*L muxes to express L writes.
//
// The _readback variants copy the entry back onto itself on the else arm. That
// is a no-op, but it makes every decoder bit drive two parallel stages joined
// by a wide mux. Real RTL writes the scatter that way far more often than the
// bare form, so a fold that only handles the single-stage shape is worth
// nothing in practice.
//
// The small pair is what the SAT self-equivalence proofs run on; the wide pair
// is the size this actually shows up at, kept for the cell-count assertions so
// the suite still gates on the real geometry without paying for a 2M-variable
// SAT problem.

module opt_vps_scatter_write #(parameter SIZE = 32, parameter LANES = 8) (
    input  logic [$clog2(SIZE)-1:0] wr_ptr,
    input  logic [7:0]              len,
    input  logic                    wen,
    input  logic [SIZE-1:0][7:0]    mem,
    input  logic [LANES*8-1:0]      din,
    output logic [SIZE-1:0][7:0]    out );
  localparam SB = $clog2(SIZE);
  logic [SB:0] p;
  always_comb begin
    out = mem;
    p = {1'b0, wr_ptr};
    if (wen)
      for (int i = 0; i < LANES; i = i + 1) begin
        p = {1'b0, wr_ptr} + (SB+1)'(i);
        if (i < {24'd0, len}) out[p[SB-1:0]] = din[i*8+:8];
      end
  end
endmodule

module opt_vps_scatter_readback #(parameter SIZE = 32, parameter LANES = 8) (
    input  logic [$clog2(SIZE)-1:0] wr_ptr,
    input  logic [7:0]              len,
    input  logic                    wen,
    input  logic [SIZE-1:0][7:0]    mem,
    input  logic [LANES*8-1:0]      din,
    output logic [SIZE-1:0][7:0]    out );
  localparam SB = $clog2(SIZE);
  logic [SB:0] p;
  always_comb begin
    out = mem;
    p = {1'b0, wr_ptr};
    if (wen)
      for (int i = 0; i < LANES; i = i + 1) begin
        p = {1'b0, wr_ptr} + (SB+1)'(i);
        if (i < {24'd0, len}) out[p[SB-1:0]] = din[i*8+:8];
        else                  out[p[SB-1:0]] = mem[p[SB-1:0]];
      end
  end
endmodule

// Real-geometry instances: a 256-entry byte array written 64 lanes at a time.
// Used for the cell-count assertions only -- proving self-equivalence at this
// size is a 2M-variable SAT problem and belongs nowhere near a regression run.
module opt_vps_scatter_write_wide (
    input  logic [7:0]        wr_ptr,
    input  logic [7:0]        len,
    input  logic              wen,
    input  logic [255:0][7:0] mem,
    input  logic [511:0]      din,
    output logic [255:0][7:0] out );
  opt_vps_scatter_write #(.SIZE(256), .LANES(64))
    u (.wr_ptr(wr_ptr), .len(len), .wen(wen), .mem(mem), .din(din), .out(out));
endmodule

module opt_vps_scatter_readback_wide (
    input  logic [7:0]        wr_ptr,
    input  logic [7:0]        len,
    input  logic              wen,
    input  logic [255:0][7:0] mem,
    input  logic [511:0]      din,
    output logic [255:0][7:0] out );
  opt_vps_scatter_readback #(.SIZE(256), .LANES(64))
    u (.wr_ptr(wr_ptr), .len(len), .wen(wen), .mem(mem), .din(din), .out(out));
endmodule
