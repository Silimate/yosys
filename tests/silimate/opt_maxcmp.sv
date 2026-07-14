// Test designs for opt_maxcmp. Combinational so equiv_opt proves each rewrite
// with a plain combinational miter, and packed-vector ports so the built-in
// Verilog frontend handles them without Verific.

// --- Positive: masked max > thr via 1<<v scatter + leading-one, 1:1 enable,
// signal threshold (the vc_congest shape). ---
module maxcmp_scatter #(parameter int N = 8, parameter int W = 4) (
  input  logic [N*W-1:0] v,
  input  logic [N-1:0]   en,
  input  logic [W-1:0]   thr,
  output logic           over
);
  logic [(1<<W)-1:0] bits;
  logic [W-1:0]      mx;
  always_comb begin
    bits = '0;
    for (int i = 0; i < N; i++)
      if (en[i]) bits[v[i*W +: W]] |= 1'b1;
    mx = '0;
    for (int i = 0; i < (1<<W); i++)
      if (bits[i]) mx = W'(i);
    over = mx > thr;
  end
endmodule

// --- Positive: broadcast enable (en[i/G]) + constant threshold. ---
module maxcmp_bcast #(parameter int N = 16, parameter int M = 4, parameter int W = 4) (
  input  logic [N*W-1:0] v,
  input  logic [M-1:0]   en,
  output logic           over
);
  localparam int G = N / M;
  logic [(1<<W)-1:0] bits;
  logic [W-1:0]      mx;
  always_comb begin
    bits = '0;
    for (int i = 0; i < N; i++)
      if (en[i/G]) bits[v[i*W +: W]] |= 1'b1;
    mx = '0;
    for (int i = 0; i < (1<<W); i++)
      if (bits[i]) mx = W'(i);
    over = mx > 4'd9;
  end
endmodule

// --- Positive: compare-select max tree (no scatter) + GE + no enable. ---
module maxcmp_tree #(parameter int N = 8, parameter int W = 6) (
  input  logic [N*W-1:0] v,
  input  logic [W-1:0]   thr,
  output logic           hi
);
  logic [W-1:0] mx;
  always_comb begin
    mx = v[0 +: W];
    for (int i = 1; i < N; i++)
      if (v[i*W +: W] > mx) mx = v[i*W +: W];
    hi = mx >= thr;
  end
endmodule

// --- Positive: min < thr (OR form via LT). ---
module maxcmp_min #(parameter int N = 8, parameter int W = 6) (
  input  logic [N*W-1:0] v,
  input  logic [W-1:0]   thr,
  output logic           lo
);
  logic [W-1:0] mn;
  always_comb begin
    mn = v[0 +: W];
    for (int i = 1; i < N; i++)
      if (v[i*W +: W] < mn) mn = v[i*W +: W];
    lo = mn < thr;
  end
endmodule

// --- Positive: max < thr (AND / all-below form). ---
module maxcmp_allbelow #(parameter int N = 8, parameter int W = 6) (
  input  logic [N*W-1:0] v,
  input  logic [W-1:0]   thr,
  output logic           alllo
);
  logic [W-1:0] mx;
  always_comb begin
    mx = v[0 +: W];
    for (int i = 1; i < N; i++)
      if (v[i*W +: W] > mx) mx = v[i*W +: W];
    alllo = mx < thr;
  end
endmodule

// --- Positive: min >= thr (AND / all-above form). ---
module maxcmp_allabove #(parameter int N = 8, parameter int W = 6) (
  input  logic [N*W-1:0] v,
  input  logic [W-1:0]   thr,
  output logic           allhi
);
  logic [W-1:0] mn;
  always_comb begin
    mn = v[0 +: W];
    for (int i = 1; i < N; i++)
      if (v[i*W +: W] < mn) mn = v[i*W +: W];
    allhi = mn >= thr;
  end
endmodule

// --- Positive: signed max > thr. ---
module maxcmp_signed #(parameter int N = 8, parameter int W = 6) (
  input  logic [N*W-1:0]      v,
  input  logic signed [W-1:0] thr,
  output logic                hi
);
  logic signed [W-1:0] mx;
  always_comb begin
    mx = $signed(v[0 +: W]);
    for (int i = 1; i < N; i++)
      if ($signed(v[i*W +: W]) > mx) mx = $signed(v[i*W +: W]);
    hi = mx > thr;
  end
endmodule

// --- Positive: threshold as a wide signal, plain max. ---
module maxcmp_sigthr #(parameter int N = 8, parameter int W = 6) (
  input  logic [N*W-1:0] v,
  input  logic [W-1:0]   thr,
  output logic           hi
);
  logic [W-1:0] mx;
  always_comb begin
    mx = v[0 +: W];
    for (int i = 1; i < N; i++)
      if (v[i*W +: W] > mx) mx = v[i*W +: W];
    hi = mx > thr;
  end
endmodule

// --- Positive: multi-bit root (per-port scatter max), two compares. ---
module maxcmp_multibit #(parameter int P = 2, parameter int N = 8, parameter int W = 5) (
  input  logic [P*N*W-1:0] v,
  input  logic [P*N-1:0]   en,
  input  logic [W-1:0]     thr,
  output logic [P-1:0]     over
);
  always_comb begin
    for (int p = 0; p < P; p++) begin
      logic [(1<<W)-1:0] bits;
      logic [W-1:0]      mx;
      bits = '0;
      for (int i = 0; i < N; i++)
        if (en[p*N + i]) bits[v[(p*N + i)*W +: W]] |= 1'b1;
      mx = '0;
      for (int i = 0; i < (1<<W); i++)
        if (bits[i]) mx = W'(i);
      over[p] = mx > thr;
    end
  end
endmodule

// --- Positive: larger fan-in, runtime sanity (still small enough for SAT). ---
module maxcmp_wide #(parameter int N = 24, parameter int W = 5) (
  input  logic [N*W-1:0] v,
  input  logic [N-1:0]   en,
  input  logic [W-1:0]   thr,
  output logic           over
);
  logic [(1<<W)-1:0] bits;
  logic [W-1:0]      mx;
  always_comb begin
    bits = '0;
    for (int i = 0; i < N; i++)
      if (en[i]) bits[v[i*W +: W]] |= 1'b1;
    mx = '0;
    for (int i = 0; i < (1<<W); i++)
      if (bits[i]) mx = W'(i);
    over = mx > thr;
  end
endmodule

// --- Negative: sum > thr is not a max/min reduction. ---
module nomatch_sum #(parameter int N = 8, parameter int W = 5) (
  input  logic [N*W-1:0] v,
  input  logic [W+3:0]   thr,
  output logic           big
);
  logic [W+3:0] s;
  always_comb begin
    s = '0;
    for (int i = 0; i < N; i++)
      s += v[i*W +: W];
    big = s > thr;
  end
endmodule

// --- Negative: xor reduction compared to a threshold (non-monotone). ---
module nomatch_xor #(parameter int N = 8, parameter int W = 5) (
  input  logic [N*W-1:0] v,
  input  logic [W-1:0]   thr,
  output logic           o
);
  logic [W-1:0] x;
  always_comb begin
    x = '0;
    for (int i = 0; i < N; i++)
      x ^= v[i*W +: W];
    o = x > thr;
  end
endmodule

// --- Negative: per-lane compares combined with XOR (no reduction anchor). ---
module nomatch_xorcmp #(parameter int N = 4, parameter int W = 5) (
  input  logic [N*W-1:0] v,
  input  logic [W-1:0]   thr,
  output logic           o
);
  always_comb begin
    o = 1'b0;
    for (int i = 0; i < N; i++)
      o ^= (v[i*W +: W] > thr);
  end
endmodule

// --- Negative: (max - min) > thr; a reduction cone but not the OR/AND idiom. ---
module nomatch_range #(parameter int N = 8, parameter int W = 6) (
  input  logic [N*W-1:0] v,
  input  logic [W-1:0]   thr,
  output logic           wide
);
  logic [W-1:0] mx, mn;
  always_comb begin
    mx = v[0 +: W];
    mn = v[0 +: W];
    for (int i = 1; i < N; i++) begin
      if (v[i*W +: W] > mx) mx = v[i*W +: W];
      if (v[i*W +: W] < mn) mn = v[i*W +: W];
    end
    wide = (mx - mn) > thr;
  end
endmodule
