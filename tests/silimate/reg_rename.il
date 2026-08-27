autoidx 1
attribute \top 1
module \top
  wire input 1 \clk
  wire input 2 \d0
  wire input 3 \d1
  wire input 4 \d2
  wire input 5 \d3
  wire input 6 \d4
  wire input 7 \d5
  wire input 8 \d6
  wire input 9 \d7
  wire input 10 \d8
  wire input 11 \d9
  wire input 12 \d10
  wire input 13 \d11
  wire \q0
  wire \q1
  wire \q2
  wire \q3
  wire \q4
  wire \q5
  wire \q6
  wire \q7
  wire \q8
  wire \q9
  wire \q10
  wire \q11
  cell $dff \q0_reg
    parameter \WIDTH 1
    parameter \CLK_POLARITY 1'1
    connect \D \d0
    connect \Q \q0
    connect \CLK \clk
  end
  cell $dff \q1_reg
    parameter \WIDTH 1
    parameter \CLK_POLARITY 1'1
    connect \D \d1
    connect \Q \q1
    connect \CLK \clk
  end
  cell $dff \q2_reg
    parameter \WIDTH 1
    parameter \CLK_POLARITY 1'1
    connect \D \d2
    connect \Q \q2
    connect \CLK \clk
  end
  cell $dff \q3_reg
    parameter \WIDTH 1
    parameter \CLK_POLARITY 1'1
    connect \D \d3
    connect \Q \q3
    connect \CLK \clk
  end
  cell $dff \q4_reg
    parameter \WIDTH 1
    parameter \CLK_POLARITY 1'1
    connect \D \d4
    connect \Q \q4
    connect \CLK \clk
  end
  cell $dff \q5_reg
    parameter \WIDTH 1
    parameter \CLK_POLARITY 1'1
    connect \D \d5
    connect \Q \q5
    connect \CLK \clk
  end
  cell $dff \q6_reg
    parameter \WIDTH 1
    parameter \CLK_POLARITY 1'1
    connect \D \d6
    connect \Q \q6
    connect \CLK \clk
  end
  cell $dff \q7_reg
    parameter \WIDTH 1
    parameter \CLK_POLARITY 1'1
    connect \D \d7
    connect \Q \q7
    connect \CLK \clk
  end
  cell $dff \q8_reg
    parameter \WIDTH 1
    parameter \CLK_POLARITY 1'1
    connect \D \d8
    connect \Q \q8
    connect \CLK \clk
  end
  cell $dff \q9_reg
    parameter \WIDTH 1
    parameter \CLK_POLARITY 1'1
    connect \D \d9
    connect \Q \q9
    connect \CLK \clk
  end
  cell $dff \q10_reg
    parameter \WIDTH 1
    parameter \CLK_POLARITY 1'1
    connect \D \d10
    connect \Q \q10
    connect \CLK \clk
  end
  cell $dff \q11_reg
    parameter \WIDTH 1
    parameter \CLK_POLARITY 1'1
    connect \D \d11
    connect \Q \q11
    connect \CLK \clk
  end
end
