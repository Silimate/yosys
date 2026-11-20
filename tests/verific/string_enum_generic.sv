// Verilog string actuals for the VHDL enumeration generics in string_enum_generic.vhd
module uses (
  output       a1, b1, m1, c1, a2, b2, m2, c2, a3, b3, m3, c3, e1,
  output [1:0] s1, s2, s3
);
  localparam P = "false";
  // Named, any case; one through a localparam; an extended identifier, with its backslashes escaped
  flags #(.A("false"), .B("TRUE"), .S("run"), .M("\\Fast\\")) u1 (.a_o(a1), .b_o(b1), .s_o(s1), .m_o(m1), .c_o(c1));
  // "a" for a character generic is position 97 in range: 'a', as before
  flags #(.A(P), .B("True"), .S("DONE"), .C("a")) u2 (.a_o(a2), .b_o(b2), .s_o(s2), .m_o(m2), .c_o(c2));
  // Ordered, and an integer actual, which still takes the literal at that position
  flags #("true", 0, "Idle") u3 (.a_o(a3), .b_o(b3), .s_o(s3), .m_o(m3), .c_o(c3));
  // A literal inside the subtype's range
  early #(.E("RUN")) u4 (.o(e1));
endmodule

module uses_ref (
  output       a1, b1, m1, c1, a2, b2, m2, c2, a3, b3, m3, c3, e1,
  output [1:0] s1, s2, s3
);
  assign {a1, b1, s1, m1, c1} = {1'b0, 1'b1, 2'b01, 1'b1, 1'b0};
  assign {a2, b2, s2, m2, c2} = {1'b0, 1'b1, 2'b10, 1'b0, 1'b1};
  assign {a3, b3, s3, m3, c3} = {1'b1, 1'b0, 2'b00, 1'b0, 1'b0};
  assign e1 = 1'b1;
endmodule

// A string that names no literal of the type
module no_literal (output a);
  flags #(.A("maybe")) u (.a_o(a));
endmodule

// A literal outside the subtype's range
module out_of_range (output o);
  early #(.E("DONE")) u (.o(o));
endmodule
