import os
import sys

sys.setdlopenflags(os.RTLD_NOW | os.RTLD_GLOBAL)

__dir__ = os.path.abspath(os.path.dirname(__file__))
sys._pyosys_dir = os.path.abspath(__dir__)

bin_ext = ".exe" if os.name == "nt" else ""

_share_candidate = os.path.join(__dir__, "share")
if os.path.isdir(_share_candidate):
    sys._pyosys_share_dirname = _share_candidate + os.path.sep

_abc_candidate = os.path.join(__dir__, f"yosys-abc{bin_ext}")
if os.path.isfile(_abc_candidate):
    sys._pyosys_abc = _abc_candidate

__all__ = ["libyosys"]


def _fsdb_reader_command():
    """Discover a packaged reader on first use, including in embedded Python."""
    from importlib.metadata import entry_points
    for provider in entry_points(group="yosys.waveform_readers", name="fsdb"):
        return provider.load()()
    return ["fsdb-reader"]
