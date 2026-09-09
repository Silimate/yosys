module ref (
    input  wire [3:0] a,
    input  wire [3:0] b,
    output wire [3:0] y,
    output wire [3:0] z
);
    assign y = ~(a | b);
    assign z = ~(a & b);
endmodule
