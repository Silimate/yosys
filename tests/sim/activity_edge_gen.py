"""Generate a VCD whose last sample is a transition, on some bits but not others.

A transition on the closing sample opens an interval of zero width, so duty never
accounts for the level it switched to. Counting it anyway reports a bit as toggling more
often than the time it was given allows, and the pair stops describing one waveform.

The window is 64 cycles of a 1GHz clock and ends exactly on a rising edge, so the clock
itself is one of the bits that toggles on the closing sample.

  clk    1GHz, rises at k*P, last rise ON the closing sample
  flip   toggles every 4 cycles, and again on the closing sample
  quiet  toggles every 4 cycles, last change well before the end
  bus    2 bits sampled together: bus[0] toggles on the closing sample, bus[1] does not

`bus` is the case that needs per-bit state rather than a per-signal timestamp: both bits
are visited at the closing sample because bus[0] changed, so a check that only asks
"was this bit written at max_time" would take a toggle off bus[1] as well, which never
changed there.

`xz` covers the other half. Its closing transition is x -> 1, worth half a toggle rather
than a whole one, so taking a whole one back off would drive its count negative.

  xz     unknown until the closing sample, where it resolves to 1
"""

import sys

PERIOD = 1_000_000  # 1ns clock in fs -> 1GHz
CYCLES = 64
END = CYCLES * PERIOD

HEADER = """$timescale 1fs $end
$scope module tb $end
$scope module uut $end
$var wire 1 ! clk $end
$var wire 1 " flip $end
$var wire 1 # quiet $end
$var wire 2 $ bus $end
$var wire 1 % xz $end
$upscope $end
$upscope $end
$enddefinitions $end
"""


def write(path):
  """Emit the dump, one timestamp section per sample that carries a change."""
  timeline = {}

  def at(t, vid, val):
    timeline.setdefault(t, []).append((vid, val))

  # clk: rises at k*P, falls at the half period. The last rise is exactly on END.
  for k in range(CYCLES + 1):
    at(k * PERIOD, "!", 1)
    if k * PERIOD + PERIOD // 2 < END:
      at(k * PERIOD + PERIOD // 2, "!", 0)

  # flip: 4-cycle square wave, plus a final flip on the closing sample.
  half = 4 * PERIOD
  t = 0
  val = 0
  while t < END:
    at(t, '"', val)
    val ^= 1
    t += half
  at(END, '"', val)

  # quiet: same 4-cycle wave, but nothing lands on the closing sample.
  t = 0
  val = 0
  while t < END:
    at(t, "#", val)
    val ^= 1
    t += half
  # bus: bit 0 flips on the closing sample, bit 1 has been settled since mid-window.
  at(0, "$", "b00")
  at(END // 2, "$", "b10")
  at(END, "$", "b11")

  # xz: unknown for the whole window, resolving to 1 on the closing sample.
  at(0, "%", "x")
  at(END, "%", 1)

  with open(path, "w", encoding="utf-8") as f:
    f.write(HEADER)
    for t in sorted(timeline):
      f.write(f"#{t}\n")
      for vid, val in timeline[t]:
        prefix = "b" if isinstance(val, str) and val.startswith("b") else ""
        f.write(f"{val}{vid}\n" if not prefix else f"{val} {vid}\n")


write(sys.argv[1])
