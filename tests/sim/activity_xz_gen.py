"""Generate a VCD whose signals spend part of the window at an unknown value.

Duty is a fraction of the time a bit was actually driven to a known 0 or 1, not of the
whole sampled window. A dump that goes dark -- a `$dumpoff`/`$dumpon` pair, or a bit an
upstream tool never drove -- would otherwise have every unknown tick counted as time
spent low, scaling duty down by the fraction of the window that survived.

Unknown stretches are written as explicit `x` values rather than `$dumpoff`, which is
the same waveform and does not depend on how the reader expands a dump-off block.

  clk    1GHz square wave, known throughout   duty 0.500  known 128M of 128M
  held   high, dark for 40M ticks mid-window  duty 1.000  known  88M of 128M
  gated  8-cycle square wave, dark after 64M  duty 0.500  known  64M of 128M
  dark   never driven                         duty 0.000  known   0

`held` and `gated` are the two cases that separate the two definitions: measuring over
the whole window instead reports 0.6875 and 0.25, both of which understate the signal by
exactly the fraction of the window that was dark. `dark` is the degenerate case, where
known time is zero and there is no duty to report -- it pins the guard that keeps that
from dividing by zero.

The stimulus is periodic over the window and every unknown interval starts and ends on a
sample, so all the expected numbers are exact (see activity_xz.ys).
"""

import sys

PERIOD = 1_000_000  # 1ns clock in fs -> 1GHz
CYCLES = 128  # window length in clock cycles
HELD_DARK = (40_000_000, 80_000_000)  # `held` is unknown over [start, stop)
GATED_DARK = 64_000_000  # `gated` is unknown from here to the end of the window

HEADER = """$timescale 1fs $end
$scope module tb $end
$scope module uut $end
$var wire 1 ! clk $end
$var wire 1 " held $end
$var wire 1 # gated $end
$var wire 1 $ dark $end
$upscope $end
$upscope $end
$enddefinitions $end
"""


def write(path):
  # time -> [(vcd_id, value)], so edges that coincide share one timestamp block
  timeline = {}

  def at(t, vid, val):
    timeline.setdefault(t, []).append((vid, val))

  # Initial sample. The first sample seeds the value; it is not a toggle.
  for vid, val in (("!", 1), ('"', 1), ("#", 0), ("$", "x")):
    at(0, vid, val)

  # Clock: high for the first half of every cycle. The final rise at CYCLES*P closes the
  # window, so the window holds exactly CYCLES high pulses of P/2.
  for k in range(CYCLES):
    at(k * PERIOD + PERIOD // 2, "!", 0)
    if k:
      at(k * PERIOD, "!", 1)
  at(CYCLES * PERIOD, "!", 1)

  # `held`: high on both sides of an unknown hole, so its known time is the window minus
  # the hole and all of it is high.
  at(HELD_DARK[0], '"', "x")
  at(HELD_DARK[1], '"', 1)

  # `gated`: 8-cycle square wave, 50% high, until it goes unknown for the rest of the
  # window. GATED_DARK lands on a whole number of periods, so the known half is exactly
  # half high.
  half = 4 * PERIOD
  t = half
  while t < GATED_DARK:
    at(t, "#", 1 if (t // half) % 2 else 0)
    t += half
  at(GATED_DARK, "#", "x")

  with open(path, "w", encoding="utf-8") as f:
    f.write(HEADER)
    for t in sorted(timeline):
      f.write(f"#{t}\n")
      for vid, val in timeline[t]:
        f.write(f"{val}{vid}\n")


write(sys.argv[1])
