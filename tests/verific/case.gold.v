/* Generated by Preqorsor 0.45+139 (git sha1 2c3d2b3ec, c++ 15.0.0 -fPIC -O3) */

(* \library  = "work" *)
(* hdlname = "top" *)
(* src = "case.sv:1.8-1.11" *)
module gold(clk, o, currentstate);
  wire _00_;
  wire _01_;
  wire _02_;
  wire _03_;
  wire [1:0] _04_;
  wire _05_;
  wire _06_;
  wire _07_;
  wire _08_;
  wire _09_;
  (* src = "case.sv:2.8-2.11" *)
  input clk;
  wire clk;
  (* src = "case.sv:3.14-3.26" *)
  input [5:0] currentstate;
  wire [5:0] currentstate;
  (* src = "case.sv:4.19-4.20" *)
  output [1:0] o;
  reg [1:0] o;
  assign _01_ = currentstate == (* src = "case.sv:17.4-17.8" *) 3'h7;
  assign _05_ = currentstate == (* src = "case.sv:9.4-9.8" *) 1'h1;
  assign _06_ = currentstate == (* src = "case.sv:9.4-9.8" *) 2'h2;
  assign _07_ = currentstate == (* src = "case.sv:9.4-9.8" *) 2'h3;
  assign _08_ = currentstate == (* src = "case.sv:13.4-13.8" *) 3'h4;
  assign _09_ = currentstate == (* src = "case.sv:17.4-17.8" *) 3'h5;
  assign _00_ = currentstate == (* src = "case.sv:17.4-17.8" *) 3'h6;
  (* src = "case.sv:6.9-26.5" *)
  always @(posedge clk)
    o <= _04_;
  assign _02_ = | (* src = "case.sv:8.3-25.10" *) { _07_, _06_, _05_ };
  assign _03_ = | (* src = "case.sv:8.3-25.10" *) { _01_, _00_, _09_ };
  function [1:0] _20_;
    input [1:0] a;
    input [5:0] b;
    input [2:0] s;
    (* src = "case.sv:8.3-25.10" *)
    (* parallel_case *)
    casez (s)
      3'b??1:
        _20_ = b[1:0];
      3'b?1?:
        _20_ = b[3:2];
      3'b1??:
        _20_ = b[5:4];
      default:
        _20_ = a;
    endcase
  endfunction
  assign _04_ = _20_(2'h0, 6'h1b, { _02_, _08_, _03_ });
endmodule
