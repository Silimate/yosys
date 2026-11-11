#!/usr/bin/env bash
# The frontend writes the type each type parameter resolved to on the module, as attribute
# type_params, in SystemVerilog that compiles in any scope. Checked against the design: declared in
# a package of its own and set with -chparam, the type elaborates the module alone to the ports and
# the logic of its instance in the design, wherever the instance's actual was declared.
set -euo pipefail
YOSYS=${YOSYS:-../../build/yosys}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

cat > $tmp/design.sv <<'EOT'
package p;
  typedef enum logic [1:0] { IDLE, RUN = 2, DONE } e_t;
  typedef struct packed { logic v; logic [3:0] d; } s_t;
  typedef struct packed { e_t a, b; } ee_t;
  typedef struct packed signed { logic [1:0] a; } ss_t;
  typedef logic [3:0] arr_t [2];
  typedef logic signed [3:0] s4;
  typedef union packed { logic [3:0] a; s4 b; } u_t;
  typedef struct { s4 a [2]; logic [1:0] b; } us_t;
endpackage
typedef logic signed [2:0] unit_t;
typedef logic flag_t;
class c_t; int x; endclass
// Logic that tells signed from unsigned, and one of p's literals in a T
module m import p::*; #(parameter type T = logic) (input T a, output T y, output T idle,
                                                   output logic lt, output logic [39:0] wide);
  assign y = a;
  assign idle = IDLE;
  assign lt = a < 0;
  assign wide = a;
endmodule
module mid #(parameter type PT = logic) (input PT a, output PT y, output PT idle,
                                         output logic lt, output logic [39:0] wide);
  m #(.T(PT)) u (.*);
endmodule
module mu #(parameter type T = logic) (input T a, output T y);
  assign y = a;
endmodule
module r #(parameter type T = logic) (input logic a, output logic y);
  assign y = a;
endmodule
module top import p::*; (input logic i, output logic o1, o2);
  typedef struct packed signed { e_t st; logic [1:0][2:0] w; } local_t;
  e_t e_a; s_t s_a, q_a; local_t l_a; unit_t n_a; e_t d_a; logic [3:0] b_a; logic [0:3] t_a;
  logic signed [-2:1] g_a; s4 [1:0] f_a; ee_t w_a; flag_t h_a; ss_t [1:0] k_a; u_t v_a;
  arr_t x_a, x_y; us_t z_a, z_y;
  m #(.T(e_t)) u_enum (.a(e_a), .y(), .idle(), .lt(), .wide());
  m #(.T(s_t)) u_struct (.a(s_a), .y(), .idle(), .lt(), .wide());
  m #(.T(p::s_t)) u_scoped (.a(q_a), .y(), .idle(), .lt(), .wide());
  m #(.T(local_t)) u_local (.a(l_a), .y(), .idle(), .lt(), .wide());
  m #(.T(unit_t)) u_unit (.a(n_a), .y(), .idle(), .lt(), .wide());
  mid #(.PT(e_t)) u_mid (.a(d_a), .y(), .idle(), .lt(), .wide());
  m #(.T(logic [3:0])) u_builtin (.a(b_a), .y(), .idle(), .lt(), .wide());
  m #(.T(logic [0:3])) u_up (.a(t_a), .y(), .idle(), .lt(), .wide());
  m #(.T(logic signed [-2:1])) u_offset (.a(g_a), .y(), .idle(), .lt(), .wide());
  m #(.T(s4 [1:0])) u_signed_elements (.a(f_a), .y(), .idle(), .lt(), .wide());
  m #(.T(ee_t)) u_enums (.a(w_a), .y(), .idle(), .lt(), .wide());
  m #(.T(flag_t)) u_flag (.a(h_a), .y(), .idle(), .lt(), .wide());
  m #(.T(ss_t [1:0])) u_signed_structs (.a(k_a), .y(), .idle(), .lt(), .wide());
  m #(.T(u_t)) u_union (.a(v_a), .y(), .idle(), .lt(), .wide());
  mu #(.T(arr_t)) u_unpacked (.a(x_a), .y(x_y));
  mu #(.T(us_t)) u_unpacked_struct (.a(z_a), .y(z_y));
  r #(.T(real)) u_real (.a(i), .y(o1));
  r #(.T(c_t)) u_class (.a(i), .y(o2));
endmodule
EOT

$YOSYS -q -p "verific -sv $tmp/design.sv; hierarchy -top top; proc; write_json $tmp/design.json
  write_rtlil $tmp/design.il"
python3 - $tmp <<'EOT'
import json, sys
tmp = sys.argv[1]
modules = json.load(open(f"{tmp}/design.json"))["modules"]
def module(path):
  name = "top"
  for cell in path.split("."):
    name = modules[name]["cells"][cell]["type"]
  return name
def written(path):
  return json.loads(modules[module(path)]["attributes"]["type_params"])
struct = "struct packed { logic v; logic [3:0] d; }"
want = {
  "u_enum": {"type": "logic [1:0]", "unpacked": ""},
  "u_struct": {"type": struct, "unpacked": ""},
  "u_scoped": {"type": struct, "unpacked": ""},
  "u_local": {"type": "struct packed signed { logic [1:0] st; logic [1:0][2:0] w; }", "unpacked": ""},
  "u_unit": {"type": "logic signed [2:0]", "unpacked": ""},
  "u_mid.u": {"type": "logic [1:0]", "unpacked": ""},
  "u_builtin": {"type": "logic [3:0]", "unpacked": ""},
  "u_up": {"type": "logic [0:3]", "unpacked": ""},
  "u_offset": {"type": "logic signed [-2:1]", "unpacked": ""},
  "u_signed_elements": {"why": "a packed array of signed elements"},
  "u_enums": {"type": "struct packed { logic [1:0] a; logic [1:0] b; }", "unpacked": ""},
  "u_flag": {"type": "logic", "unpacked": ""},
  "u_signed_structs": {"type": "struct packed signed { logic [1:0] a; } [1:0]", "unpacked": ""},
  "u_union": {"type": "union packed { logic [3:0] a; logic signed [3:0] b; }", "unpacked": ""},
  "u_unpacked": {"type": "logic [3:0]", "unpacked": "[0:1]"},
  "u_unpacked_struct": {"type": "struct { logic signed [3:0] a[0:1]; logic [1:0] b; }", "unpacked": ""},
  "u_real": {"why": "type real"},
  "u_class": {"why": "type c_t, which may not be integral"},
}
for path, type_ in want.items():
  assert written(path) == {"T": type_}, (path, written(path))
assert written("u_mid") == {"PT": {"type": "logic [1:0]", "unpacked": ""}}, written("u_mid")
assert "type_params" not in modules["top"]["attributes"]
# Each type that is written, declared on its own; with the module of the instance to compare
with open(f"{tmp}/written", "w") as cases:
  for path, type_ in want.items():
    if "type" in type_:
      open(f"{tmp}/{path}.sv", "w").write(f"package tp; typedef {type_['type']} T {type_['unpacked']}; endpackage\n")
      print(path, module(path), module(path).split("(")[0], file=cases)
EOT

# The instance's module and the module alone, elaborated at the written type: same ports, and
# equivalent
while read -r path instance name; do
  $YOSYS -q -p "verific -sv $tmp/$path.sv $tmp/design.sv; hierarchy -top $name -chparam T tp::T; proc
    rename $name gate; read_rtlil $tmp/design.il; rename $instance gold; write_json $tmp/$path.json
    miter -equiv -flatten -make_assert gold gate miter; sat -verify -prove-asserts miter"
done < $tmp/written
python3 - $tmp <<'EOT'
import json, sys
tmp = sys.argv[1]
def ports(module):
  return [(p, v["direction"], len(v["bits"]), v.get("upto", 0), v.get("offset", 0), v.get("signed", 0))
          for p, v in module["ports"].items()]
for path in (line.split()[0] for line in open(f"{tmp}/written")):
  modules = json.load(open(f"{tmp}/{path}.json"))["modules"]
  assert ports(modules["gate"]) == ports(modules["gold"]), (path, ports(modules["gate"]), ports(modules["gold"]))
EOT
