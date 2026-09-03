// A write pointer reset to 0 and only ever stepped by an aligned burst length keeps a
// zero tail in every reachable state, so its low $clog2(COLS) bits are constants even
// though the pointer itself is not.
//
// That tail is what makes the scatter below expensive. As written, each of the COLS
// writes lands at a variable offset, so Verific unrolls the loop into COLS successive
// conditional updates of the whole array: ROWS*COLS*COLS byte muxes, a full crossbar.
// Once the tail folds, the column index of iteration i is the constant i and the whole
// thing is a plain write of one row.
module opt_seqconst_align #(
    parameter int ROWS = 4,
    parameter int COLS = 8,
    parameter int EW   = 4
  ) (
    input  logic                              clk,
    input  logic                              rst,
    input  logic                              wr,
    input  logic [COLS-1:0][EW-1:0]           wrdata,
    output logic [ROWS-1:0][COLS-1:0][EW-1:0] mem
  );

  localparam int PW = $clog2(ROWS*COLS);
  localparam int RW = $clog2(ROWS);
  localparam int CW = $clog2(COLS);

  logic [PW-1:0] wr_ptr, wr_ptr_next, ptr_t;
  logic [ROWS-1:0][COLS-1:0][EW-1:0] mem_next;

  always_comb begin
    wr_ptr_next = wr_ptr;
    if (wr) wr_ptr_next = PW'(wr_ptr + COLS);
  end

  always_comb begin
    mem_next = mem;
    ptr_t = PW'(0);
    if (wr)
      for (int i = 0; i < COLS; i++) begin
        ptr_t = PW'(wr_ptr + i);
        mem_next[ptr_t[CW+:RW]][ptr_t[CW-1:0]] = wrdata[i];
      end
  end

  // Async reset, as the library flops of the design this models use, so the reset
  // value lands on the cell rather than in a mux on D.
  always_ff @(posedge clk or posedge rst)
    if (rst) begin
      wr_ptr <= '0;
      mem    <= '0;
    end else begin
      wr_ptr <= wr_ptr_next;
      mem    <= mem_next;
    end

endmodule
