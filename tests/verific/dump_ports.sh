#!/usr/bin/env bash
# verific -dump-ports writes a module's port declarations, unelaborated, so they compile on their
# own. Checked against the module itself: alone, with the declarations they need, and as a wrapper
# that connects to the module by name, they elaborate to the module's ports.
set -euo pipefail
YOSYS=${YOSYS:-../../build/yosys}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

cat > $tmp/pkg.sv <<'EOT'
`define ST_W 2
package base_pkg;
  localparam int K = 2;
endpackage
package bank_pkg;
  import base_pkg::*;
  localparam int BANKS = 4;  // one entry each
  typedef logic [K-1:0] off_t;
  typedef struct packed { logic [3:0] seg; off_t off; } ent_t;
  typedef enum logic [`ST_W-1:0] { IDLE, BUSY } st_t;
  typedef struct { logic [1:0] a; logic b; } pair_t;
  typedef struct packed { enum logic { LO, HI } lvl; logic v; } tag_t;
endpackage
interface inner_if; logic x; endinterface
interface bus_if; import base_pkg::*; inner_if in(); logic [K-1:0] d; modport mp(input d); endinterface
EOT

cat > $tmp/top.sv <<'EOT'
`define NUM 4
localparam int SW = 1;
typedef enum logic [SW-1:0] { OFF, ON } sw_t;
typedef logic [2:0] tri_t;
module top import bank_pkg::*; #(parameter W = 8, parameter type T = logic [1:0],
                                 localparam L = W + 1) (
  input                    clk,
  input  ent_t             e [BANKS],
  input  tri_t [1:0]       t,
  input  [`NUM-1:0][W-1:0] v,
  input  wire logic [2:0]  n,
  input  T                 tp,
  input  st_t              s,
  input  pair_t            p,
  input  tag_t             g,
  input  sw_t              sw,
  input  logic             \input ,
`ifdef DEBUG
  input  logic             dbg,
`endif
  output logic signed [W-1:0] y [0:1]
);
endmodule
module old (a, b, y);
  parameter N = 3;
  input [N-1:0] a;
  input bank_pkg::off_t b [2];
  output reg y;
endmodule
module bused (bus_if.mp b, output \o.k );
endmodule
module none;
endmodule
module renamed (.q(x));
  input [3:0] x;
endmodule
module part (x[1:0]);
  input [3:0] x;
endmodule
module named_ansi (input [3:0] a, output .p(r[1:0]));
  logic [3:0] r;
endmodule
module unknown #(parameter N = 'x) (input [N:0] a);
endmodule
EOT

# Names that are SystemVerilog keywords, from a Verilog-2001 analysis, escaped
cat > $tmp/old.v <<'EOT'
module keywords (logic, bit);
  input logic;
  input [1:0] bit;
endmodule
EOT

$YOSYS -q -p "verific -sv $tmp/pkg.sv $tmp/top.sv
  verific -dump-ports -chparam W 6 -chparam W 4 $tmp/top.json top
  verific -dump-ports $tmp/old.json old
  verific -dump-ports $tmp/bused.json bused
  verific -dump-ports $tmp/none.json none
  verific -vlog2k $tmp/old.v
  verific -dump-ports $tmp/keywords.json keywords
  select -assert-mod-count 0 *
  verific -import top; write_json $tmp/default.json"
python3 - $tmp <<'EOT'
import json, sys
tmp = sys.argv[1]
top, old, bused, none, keywords = (json.load(open(f"{tmp}/{m}.json"))
                                   for m in ("top", "old", "bused", "none", "keywords"))
assert keywords["ports"] == ["input \\logic ", "input [1:0] \\bit "], keywords
assert top["ports"] == [
  "input clk",
  "input struct packed { logic [3:0] seg; logic [1:0] off; } e[4]",
  "input logic [1:0][2:0] t",
  "input [3:0][3:0] v",
  "input wire logic [2:0] n",
  "input logic [1:0] tp",
  "input bank_pkg::st_t s",
  "input bank_pkg::pair_t p",
  "input bank_pkg::tag_t g",
  "input sw_t sw",
  "input logic \\input ",
  "output logic signed [3:0] y[0:1]",
], top["ports"]
base, bank, *unit = top["declarations"]
assert base == "package base_pkg;\n  localparam int K = 2;\nendpackage", base
# A macro in its source, so as Verific prints it
assert bank.strip().startswith("package bank_pkg") and "`" not in bank, bank
# All the compilation unit's declarations, for its enum
assert unit == ["localparam int SW = 1;", "typedef enum logic [SW-1:0] { OFF, ON } sw_t;",
                "typedef logic [2:0] tri_t;"], unit
assert old == {"ports": ["input [2:0] a", "input logic [1:0] b[2]", "output reg y"],
               "declarations": []}, old
assert bused["ports"] == ["bus_if.mp b", "output \\o.k "], bused
# The names they declare, in order
assert [d.split()[1].rstrip(";") for d in bused["declarations"]] == [
  "inner_if", "base_pkg", "bus_if"], bused["declarations"]
assert none == {"ports": [], "declarations": []}, none
# After -chparam W given twice, the import still elaborates at W's default, 8
y = json.load(open(f"{tmp}/default.json"))["modules"]["top"]["ports"]["y[0]"]
assert len(y["bits"]) == 8, y

for name, json_ in (("top", top), ("bused", bused)):
  ports = ",\n  ".join(json_["ports"])
  open(f"{tmp}/{name}_alone.sv", "w").write(
    "\n".join(json_["declarations"]) + f"\nmodule {name} (\n  {ports}\n);\nendmodule\n")
  setting = " #(.W(4))" if name == "top" else ""
  open(f"{tmp}/{name}_wrap.sv", "w").write(
    f"module {name}_wrap (\n  {ports}\n);\n  {name}{setting} u_{name} (.*);\nendmodule\n")
EOT

for name in top bused; do
  $YOSYS -q -p "verific -sv $tmp/${name}_alone.sv; verific -import $name; write_json $tmp/${name}_alone.json"
  $YOSYS -q -p "verific -sv $tmp/pkg.sv $tmp/top.sv $tmp/${name}_wrap.sv; verific -import ${name}_wrap
    write_json $tmp/${name}_wrap.json"
done
python3 - $tmp <<'EOT'
import json, sys
tmp = sys.argv[1]
def ports(path, name):
  # Verific names a module elaborated with parameters set <name>(<parameters>)
  module = next(m for n, m in json.load(open(path))["modules"].items()
                if n == name or n.startswith(f"{name}("))
  return [(p, v["direction"], len(v["bits"])) for p, v in module["ports"].items()]
for name in ("top", "bused"):
  want, alone = ports(f"{tmp}/{name}_wrap.json", name), ports(f"{tmp}/{name}_alone.json", name)
  assert alone == want, (name, alone)
  assert ports(f"{tmp}/{name}_wrap.json", f"{name}_wrap") == want, name
EOT

# What can't be written is refused: <options>|<module>|<error>
for case in "-chparam L 1|top|no parameter 'L'" "|renamed|isn't a declaration of its own" \
            "|part|isn't a declaration of its own" "|named_ansi|isn't a declaration of its own" \
            "|unknown|Cannot evaluate the dimension" "|base_pkg|is not a module" \
            "|bus_if|is not a module"; do
  IFS='|' read -r options module error <<< "$case"
  $YOSYS -q -p "verific -sv $tmp/pkg.sv $tmp/top.sv
    logger -expect error \"$error\" 1
    verific -dump-ports $options $tmp/refused.json $module" 2> /dev/null
done
