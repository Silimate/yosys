#!/usr/bin/env bash
# -missing-input-file writes every input port missing from the replayed dump as JSON, with no
# cap, while the log keeps naming only the first 20.
set -euo pipefail
YOSYS=${YOSYS:-../../build/yosys}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# sim converts a VCD to <tmpdir>/converted_<basename>.fst, so tests running in parallel on the
# same dump race on that file: replay private copies under names no other test uses.
cp missing_input.vcd $tmp/mif_missing_input.vcd
cp array_port_1d_bits.vcd $tmp/mif_array_port_1d_bits.vcd

# check <json> <python expression over `d`>
check() {
	python3 -c 'import json, sys; d = json.load(open(sys.argv[1])); assert eval(sys.argv[2]), (sys.argv[2], d)' "$1" "$2"
}

# 1. One missing port under -missing-input-warn
$YOSYS -q -p "read_verilog missing_input.v; prep -top missing_input
	sim -r $tmp/mif_missing_input.vcd -scope missing_input -q -missing-input-warn -missing-input-file $tmp/one.json"
check $tmp/one.json 'd["count"] == 1 and d["bits"] == 1'
check $tmp/one.json 'd["missing_inputs"] == [{"module": "missing_input", "path": "missing_input.b", "width": 1}]'

# 2. Still fatal without -missing-input-warn, with the error naming the port as before, but only
#    once the file has been written
if $YOSYS -q -l $tmp/fatal.log -p "read_verilog missing_input.v; prep -top missing_input
	sim -r $tmp/mif_missing_input.vcd -scope missing_input -q -missing-input-file $tmp/fatal.json" >/dev/null 2>&1; then
	echo "missing input was not fatal"; exit 1
fi
grep -q "Can't find port 'missing_input.b' on module 'missing_input' in FST. Use -missing-input-warn" $tmp/fatal.log
check $tmp/fatal.json 'd["count"] == 1 and d["missing_inputs"][0]["path"] == "missing_input.b"'

# 3. Nothing missing: the file still says so, and every array element bound
$YOSYS -q -p "read_verilog array_port.v; prep -top array_port_1d
	sim -r $tmp/mif_array_port_1d_bits.vcd -scope tb.dut -q -sim-cmp -missing-input-file $tmp/none.json"
check $tmp/none.json 'd == {"count": 0, "bits": 0, "missing_inputs": [], "mismatched_inputs": [], "undriven_signals": []}'

# 4. 25 array element ports genuinely absent from the dump, past the 20 the log names: all of them
#    are in the file, with their declared (negative) indices
{
	echo "module absent_array ("
	for i in $(seq -12 12); do echo "	input wire [1:0] \\gone[$i] ,"; done
	echo "	input wire a, output wire out);"
	echo "	assign out = a;"
	echo "endmodule"
} > $tmp/absent_array.v
$YOSYS -q -l $tmp/many.log -p "read_verilog $tmp/absent_array.v; prep -top absent_array
	sim -r $tmp/mif_missing_input.vcd -scope missing_input -q -missing-input-warn -missing-input-file $tmp/many.json"
test "$(grep -c "Can't find port '.*' on module 'absent_array' in FST, leaving it undriven." $tmp/many.log)" = 20
grep -q "5 further input port(s) missing from the FST are left undriven." $tmp/many.log
check $tmp/many.json 'd["count"] == 25 and d["bits"] == 50'
check $tmp/many.json 'sorted(m["path"] for m in d["missing_inputs"]) == sorted("missing_input.gone[%d]" % i for i in range(-12, 13))'
check $tmp/many.json 'all(m["module"] == "absent_array" and m["width"] == 2 for m in d["missing_inputs"])'

# 5. A port the dump holds under its own name but narrower than declared: bound on the bits the
#    two widths share, so it is listed as mismatched rather than missing
{
	echo "module narrow_port (input wire [3:0] a, output wire out);"
	echo "	assign out = ^a;"
	echo "endmodule"
} > $tmp/narrow_port.v
$YOSYS -q -l $tmp/narrow.log -p "read_verilog $tmp/narrow_port.v; prep -top narrow_port
	sim -r $tmp/mif_missing_input.vcd -scope missing_input -q -missing-input-warn -missing-input-file $tmp/narrow.json"
grep -q "Port 'missing_input.a' on module 'narrow_port' is 1 bit(s) in the FST and 4 in the netlist; driving the low 1 bit(s)." $tmp/narrow.log
check $tmp/narrow.json 'd["missing_inputs"] == []'
check $tmp/narrow.json 'd["mismatched_inputs"] == [{"module": "narrow_port", "path": "missing_input.a", "width": 4, "fst_width": 1}]'

# 6. A dumped signal the netlist does not drive is listed under undriven_signals, from every
#    -instance root and not only the first
cat > $tmp/two_roots.vcd <<'VCD'
$scope module first $end
$var wire 1 ! a $end
$var wire 1 " b $end
$var wire 1 # out $end
$upscope $end
$scope module second $end
$var wire 1 $ in $end
$var wire 1 % out $end
$var wire 1 & undrv $end
$upscope $end
$enddefinitions $end
#0
0!
0"
0#
0$
0%
1&
#10
1!
1"
1#
1$
1%
0&
VCD
$YOSYS -q -l $tmp/two_roots.log -p "read_verilog missing_input.v undriven_replay.v; proc
	sim -r $tmp/two_roots.vcd -instance missing_input:first -instance undriven_replay:second -q -undriven-warn -missing-input-file $tmp/two_roots.json"
grep -q "Input trace contains undriven signal \`second.undrv\`" $tmp/two_roots.log
check $tmp/two_roots.json 'd["undriven_signals"] == [{"module": "undriven_replay", "path": "second.undrv", "bits": 1, "width": 1}]'

# 7. A port the dump holds wider than declared is driven on its low bits, and listed as
#    mismatched too, since which of the dumped bits belong to the port is a guess
cat > $tmp/wide.vcd <<'VCD'
$scope module wide_port $end
$var wire 4 ! w [3:0] $end
$upscope $end
$enddefinitions $end
#0
b0000 !
#10
b1111 !
VCD
{
	echo "module wide_port (input wire [1:0] w, output wire out);"
	echo "	assign out = ^w;"
	echo "endmodule"
} > $tmp/wide_port.v
$YOSYS -q -p "read_verilog $tmp/wide_port.v; prep -top wide_port
	sim -r $tmp/wide.vcd -scope wide_port -q -missing-input-warn -missing-input-file $tmp/wide.json"
check $tmp/wide.json 'd["missing_inputs"] == []'
check $tmp/wide.json 'd["mismatched_inputs"] == [{"module": "wide_port", "path": "wide_port.w", "width": 2, "fst_width": 4}]'

# 8. -bind-only writes the same file from the binding alone and stops before replaying anything
$YOSYS -q -l $tmp/replay.log -p "read_verilog missing_input.v; prep -top missing_input
	sim -r $tmp/mif_missing_input.vcd -scope missing_input -missing-input-warn -missing-input-file $tmp/replay.json"
$YOSYS -q -l $tmp/bind_only.log -p "read_verilog missing_input.v; prep -top missing_input
	sim -r $tmp/mif_missing_input.vcd -scope missing_input -missing-input-warn -bind-only -missing-input-file $tmp/bind_only.json"
grep -q "Co-simulation from" $tmp/replay.log
if grep -q "Co-simulation from" $tmp/bind_only.log; then echo "-bind-only replayed the dump"; exit 1; fi
check $tmp/bind_only.json 'd == json.load(open(sys.argv[1].replace("bind_only", "replay")))'

# 9. -bind-only with no file to write, or a replay that is not FST/VCD, is an error
if $YOSYS -q -l $tmp/no_file.log -p "read_verilog missing_input.v; prep -top missing_input
	sim -r $tmp/mif_missing_input.vcd -scope missing_input -missing-input-warn -bind-only" 2>/dev/null; then
	echo "-bind-only ran without -missing-input-file"; exit 1
fi
grep -q "requires FST/VCD cosim" $tmp/no_file.log
if $YOSYS -q -l $tmp/witness.log -p "read_verilog missing_input.v; prep -top missing_input
	sim -r $tmp/none.yw -missing-input-warn -bind-only -missing-input-file $tmp/witness.json" 2>/dev/null; then
	echo "-bind-only replayed a witness file"; exit 1
fi
grep -q "requires FST/VCD cosim" $tmp/witness.log
