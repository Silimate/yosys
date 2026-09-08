// Two variable-part-select reads of one register whose indices are stage 1 and
// stage 2 of the SAME pipeline. They hold different values, but tracing either
// one back through the flops reaches the same roots, {clk, index}. Grouping on
// that traced root set put both reads in one barrel-shifter group, and the
// merge builds the shared shifter from a single group member's shift signal --
// so q1 silently became q0. Keying on the affine form keeps them apart: idx1
// and idx2 are distinct atoms.
module opt_vps_pipe_idx (
    input  logic         clk,
    input  logic         wr_en,
    input  logic [7:0]   index,
    input  logic [255:0] wdata,
    output logic [31:0]  q0,
    output logic [31:0]  q1
);
    logic [255:0] reg_data;
    logic [7:0]   idx1, idx2;

    always_ff @(posedge clk) begin
        if (wr_en)
            reg_data <= wdata;
        idx1 <= index;
        idx2 <= idx1;
    end

    assign q0 = reg_data[idx1 +: 32];
    assign q1 = reg_data[idx2 +: 32];
endmodule
