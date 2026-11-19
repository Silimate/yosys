// A parameterized class reaches a type through its type parameter T: typedef T::y x, or a typedef
// inherited from a base class that is T. C#(A)::x is then A::y, per specialization (IEEE 1800-2017
// 8.25.1), as chipsalliance/i3c-core's csr_cfg_extractor uses it.
package cfg_pkg;
  class cfg_a; typedef struct packed { logic [7:0] x; logic v; } data_t; endclass
  class cfg_b; typedef struct packed { logic [15:0] x; logic v; } data_t; endclass
  class extractor #(type T); typedef T::data_t data_t; endclass
  class extractor_def #(int N = 1, type T = cfg_a); typedef T::data_t data_t; endclass
  class inherit #(type T) extends T; endclass
  class chain #(type U); typedef extractor#(U)::data_t data_t; endclass
  class dep #(type U = cfg_a, type T = U); typedef T::data_t data_t; endclass
endpackage

module sub import cfg_pkg::*; #(
    parameter type cfg_t = cfg_a,
    parameter type data_t = extractor#(cfg_t)::data_t,
    parameter type named_t = extractor#(.T(cfg_t))::data_t,
    parameter type pos_t = extractor_def#(2, cfg_t)::data_t,
    parameter type def_t = extractor_def#()::data_t,
    parameter type pkg_t = cfg_pkg::extractor#(cfg_t)::data_t,
    parameter type inh_t = inherit#(cfg_t)::data_t,
    parameter type chain_t = chain#(cfg_t)::data_t,
    parameter type dep_t = dep#(.U(cfg_t))::data_t,
    parameter type depdef_t = dep#()::data_t
) (
    input logic [31:0] d,
    output data_t q,
    output logic [15:0] x,
    output logic [71:0] w
);
  typedef extractor#(cfg_t)::data_t local_t;
  assign q = d;
  assign x = q.x;
  // $bits of each form, a byte each, the first in the low byte
  assign w = {8'($bits(depdef_t)), 8'($bits(dep_t)), 8'($bits(local_t)), 8'($bits(chain_t)),
              8'($bits(inh_t)), 8'($bits(pkg_t)), 8'($bits(def_t)), 8'($bits(pos_t)),
              8'($bits(named_t))};
endmodule

module top import cfg_pkg::*; (
    input logic [31:0] d,
    output logic [31:0] qa, qb,
    output logic [15:0] xa, xb,
    output logic [71:0] wa, wb
);
  sub #(.cfg_t(cfg_a)) ua (.d, .q(qa), .x(xa), .w(wa));
  sub #(.cfg_t(cfg_b)) ub (.d, .q(qb), .x(xb), .w(wb));
endmodule

// cfg_a declares no nope_t: an error once the class is specialized (class_type_param_scope_err.ys)
module bad import cfg_pkg::*; #(
    parameter type cfg_t = cfg_a,
    parameter type nope_t = inherit#(cfg_t)::nope_t
) (input nope_t d, output nope_t q);
  assign q = d;
endmodule
