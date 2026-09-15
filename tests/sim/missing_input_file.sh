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
check $tmp/none.json 'd == {"count": 0, "bits": 0, "missing_inputs": []}'

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
