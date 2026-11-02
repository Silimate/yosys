from pathlib import Path
from tempfile import TemporaryDirectory
from pyosys import libyosys as ys

# opt_balance_tree removes the chain it replaced from the design it ran on, also
# when that is not the global design
design = ys.Design()
with TemporaryDirectory() as tmp:
	top = Path(tmp) / "top.v"
	top.write_text("module top(input [3:0] a, b, c, d, output [3:0] x); assign x = a + b + c + d; endmodule\n")
	design.run_pass(["read_verilog", str(top)])
design.run_pass("opt_balance_tree")
design.run_pass("select -assert-count 3 t:$add")
