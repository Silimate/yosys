import json
import os
import shutil
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

from pyosys import libyosys as ys


if os.name != "posix" or not hasattr(ys, "FsdbChanges"):
    sys.exit(0)


def simulate(waveform, rtl, fast, output):
    design = ys.Design()
    design.run_pass(["read_verilog", str(rtl)])
    design.run_pass("prep -top activity_window")
    command = ["sim", "-r", str(waveform), "-scope", "tb.uut", "-activity", "-q",
               "-start", "16ns", "-stop", "96ns"]
    design.run_pass(command + (["-fast"] if fast else []))
    design.run_pass(["write_json", str(output)])
    module = json.loads(output.read_text())["modules"]["activity_window"]
    return {name: net["attributes"]["$DUTY"] for name, net in module["netnames"].items()
            if "$DUTY" in net["attributes"]}


with tempfile.TemporaryDirectory() as directory:
    root = Path(directory)
    reader = root / "external reader"
    reader.write_text("""#!/usr/bin/env python3
import json
import sys
from pathlib import Path
header, events = json.loads(Path(sys.argv[2]).read_text())
if sys.argv[1] == "--header":
    for row in header:
        print(json.dumps(row))
else:
    selected = set(map(int, sys.stdin))
    for tick, handle, value in events:
        if tick <= int(sys.argv[3]) and handle in selected:
            print(tick, handle, value)
""")
    reader.chmod(0o755)
    os.environ["YOSYS_FSDB_READER"] = str(reader)
    waveform = root / "test recording.FSDB"
    header = [["time", -12, "0", "20"], ["var", 1, "dut", "clk", 1, False],
              ["var", 2, "dut", "data[1:0]", 2, True]]
    events = [(0, 2, "xz"), (10, 1, "1"), (10, 2, "10")]
    waveform.write_text(json.dumps([header, events]))
    scale, start, end, signals = ys.waveform_info(str(waveform))
    assert (scale, start, end) == (-12, 0, 20)
    assert signals == [(1, "dut", "clk", 1), (2, "dut", "data[1:0]", 2)]
    assert list(ys.FsdbChanges(str(waveform), [2], 10)) == [(0, 2, "xz"), (10, 2, "10")]
    header[0][-1] = "100"
    waveform.write_text(json.dumps([header, events]))
    assert ys.waveform_info(str(waveform))[2] == 100
    fixtures = Path(__file__).resolve().parents[1] / "sim"
    vcd = fixtures / "activity_window_base.vcd"
    variables = {}
    header = [["time", -15, "0", "128000000"]]
    events = []
    for line in vcd.read_text().splitlines():
        if line.startswith("$var"):
            _, _, _, code, name, _ = line.split()
            handle = len(variables) + 1
            variables[code] = handle
            header.append(["var", handle, "tb.uut", name, 1, False])
        elif line.startswith("#"):
            tick = int(line[1:])
        elif line[:1] in ("0", "1"):
            events.append((tick, variables[line[1:]], line[0]))
    waveform.write_text(json.dumps([header, events]))
    rtl = fixtures / "activity_window.v"
    reference = None
    if shutil.which("vcd2fst"):
        uppercase = root / "reference.VCD"
        shutil.copyfile(vcd, uppercase)
        reference = simulate(uppercase, rtl, False, root / "vcd.json")
    for fast in (False, True):
        duty = simulate(waveform, rtl, fast, root / "fsdb.json")
        # Input c is set once at time zero; its value must survive the window start.
        assert float(duty["c"].strip()) == 1.0
        assert 0.4 < float(duty["y"].strip()) < 0.6
        if reference is None:
            reference = duty
        assert duty == reference

    del os.environ["YOSYS_FSDB_READER"]
    class Provider:
        def load(self):
            return lambda: [str(reader)]

    with patch("importlib.metadata.entry_points", return_value=[Provider()]) as providers:
        assert list(ys.FsdbChanges(str(waveform), [1], 0)) == [(0, 1, "1")]
        providers.assert_called_once_with(group="yosys.waveform_readers", name="fsdb")
    (root / "fsdb-reader").symlink_to(reader)
    os.environ["PATH"] = str(root) + os.pathsep + os.environ["PATH"]
    with patch("importlib.metadata.entry_points", return_value=[]):
        assert list(ys.FsdbChanges(str(waveform), [1], 0)) == [(0, 1, "1")]
    os.environ["YOSYS_FSDB_READER"] = str(reader)
    reader.write_text("#!/bin/sh\nexit 3\n")
    try:
        list(ys.FsdbChanges(str(waveform), [1], 10))
    except RuntimeError as error:
        assert "FSDB reader failed" in str(error)
    else:
        raise AssertionError("reader failure was treated as EOF")
