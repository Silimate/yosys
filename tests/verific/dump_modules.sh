#!/usr/bin/env bash
# verific -dump-modules lists each analyzed module's ports and the modules it instantiates, in
# generate branches and undefined ones too, leaving out packages and elaborating nothing.
set -euo pipefail
YOSYS=${YOSYS:-../../build/yosys}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

cat > $tmp/dump_modules.sv <<'EOT'
package pkg;
  localparam W = 2;
endpackage
module leaf(a, y);
  input a;
  output y;
  assign y = ~a;
endmodule
module top #(parameter MEM = 0) (input a, output y);
  leaf u(.a(a), .y(y));
  generate if (MEM) begin : g
    sram u_ram(.a(a));
  end endgenerate
endmodule
EOT

$YOSYS -q -p "verific -sv $tmp/dump_modules.sv; verific -dump-modules $tmp/modules.json; select -assert-mod-count 0 *"
python3 - $tmp/modules.json <<'EOT'
import json, os, sys
modules = json.load(open(sys.argv[1]))
for unit in modules.values():
  unit["file"] = os.path.basename(unit["file"])
assert modules == {
  "leaf": {"file": "dump_modules.sv", "ports": ["a", "y"], "instances": []},
  "top": {"file": "dump_modules.sv", "ports": ["a", "y"], "instances": ["leaf", "sram"]},
}, modules
EOT
