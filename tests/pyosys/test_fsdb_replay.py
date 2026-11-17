import os
import tempfile
from pathlib import Path

from pyosys import libyosys as ys


with tempfile.TemporaryDirectory() as directory:
    root = Path(directory)
    reader = root / "external reader"
    reader.write_text("""#!/usr/bin/env python3
import json
import sys
from pathlib import Path
filename = Path(sys.argv[2])
if sys.argv[1] == "--header":
    print(json.dumps(["time", -12, "0", filename.read_text()]))
    print(json.dumps(["var", 1, "dut", "clk", 1, False]))
    print(json.dumps(["var", 2, "dut", "data[1:0]", 2, True]))
else:
    selected = set(map(int, sys.stdin))
    for tick, handle, value in [(0, 2, "xz"), (10, 1, "1"), (10, 2, "10")]:
        if tick <= int(sys.argv[3]) and handle in selected:
            print(tick, handle, value)
""")
    reader.chmod(0o755)
    os.environ["YOSYS_FSDB_READER"] = str(reader)
    waveform = root / "test recording.FSDB"
    waveform.write_text("20")
    scale, start, end, signals = ys.waveform_info(str(waveform))
    assert (scale, start, end) == (-12, 0, 20)
    assert signals == [(1, "dut", "clk", 1), (2, "dut", "data[1:0]", 2)]
    assert list(ys.FsdbChanges(str(waveform), [2], 10)) == [(0, 2, "xz"), (10, 2, "10")]
    waveform.write_text("100")
    assert ys.waveform_info(str(waveform))[2] == 100
    reader.write_text("#!/bin/sh\nexit 3\n")
    try:
        list(ys.FsdbChanges(str(waveform), [1], 10))
    except RuntimeError as error:
        assert "FSDB reader failed" in str(error)
    else:
        raise AssertionError("reader failure was treated as EOF")
