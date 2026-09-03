# A constant shift amount with bit 31 set, which as_int() would hand back as a
# negative native int. Written as RTLIL because no HDL frontend will hand you a
# surviving shift by 2**31.
#
# `a` is all ones and signed, and the shift is oversized, so `y` is 0000 and `q`
# leaves its reset value of 1111 after one clock: it is not constant and must not
# fold. Read the amount as negative and the evaluator indexes `a` past its top
# instead, which for a signed operand reads back as the sign bit, making `y` look
# like 1111 and `q` like a constant.
autoidx 1

module \shiftovf
  wire input 1 \clk
  wire input 2 \rst
  wire width 1 \s
  wire width 4 \a
  wire width 4 \y
  wire width 4 output 3 \q

  connect \a { \s \s \s \s }

  cell $adff \s_reg
    parameter \ARST_POLARITY 1'1
    parameter \ARST_VALUE 1'1
    parameter \CLK_POLARITY 1'1
    parameter \WIDTH 1
    connect \ARST \rst
    connect \CLK \clk
    connect \D \s
    connect \Q \s
  end

  cell $shl \sh
    parameter \A_SIGNED 1
    parameter \A_WIDTH 4
    parameter \B_SIGNED 0
    parameter \B_WIDTH 32
    parameter \Y_WIDTH 4
    connect \A \a
    connect \B 32'10000000000000000000000000000000
    connect \Y \y
  end

  cell $adff \q_reg
    parameter \ARST_POLARITY 1'1
    parameter \ARST_VALUE 4'1111
    parameter \CLK_POLARITY 1'1
    parameter \WIDTH 4
    connect \ARST \rst
    connect \CLK \clk
    connect \D \y
    connect \Q \q
  end
end
