yosys -import
read_verilog clockgate.v
read_verilog ../sim/sdffe.v
yosys proc
opt

design -save before

#------------------------------------------------------------------------------

# Test -pos

clockgate -pos pdk_icg ce:clkin:clkout -tie_lo scanen

# falling edge clock flops don't get matched on -pos
select -module dffe_00 -assert-count 0 t:\\pdk_icg
select -module dffe_01 -assert-count 0 t:\\pdk_icg
# rising edge clock flops do get matched on -pos
select -module dffe_10 -assert-count 1 t:\\pdk_icg
select -module dffe_11 -assert-count 1 t:\\pdk_icg
# if necessary, EN is inverted, since the given ICG
# is assumed to have an active-high EN
select -module dffe_10 -assert-count 1 t:\$_NOT_
select -module dffe_11 -assert-count 0 t:\$_NOT_

# Extra credit: multi-bit FFs work fine as well
select -module dffe_wide_11 -assert-count 1 t:\\pdk_icg

#------------------------------------------------------------------------------

# Test -neg

design -load before
clockgate -min_net_size 1 -neg pdk_icg ce:clkin:clkout -tie_lo scanen

# falling edge clock flops do get matched on -neg
select -module dffe_00 -assert-count 1 t:\\pdk_icg
select -module dffe_01 -assert-count 1 t:\\pdk_icg
# rising edge clock flops don't get matched on -neg
select -module dffe_10 -assert-count 0 t:\\pdk_icg
select -module dffe_11 -assert-count 0 t:\\pdk_icg
# if necessary, EN is inverted, since the given ICG
# is assumed to have an active-high EN
select -module dffe_00 -assert-count 1 t:\$_NOT_
select -module dffe_01 -assert-count 0 t:\$_NOT_

#------------------------------------------------------------------------------

# Same as first case, but on fine-grained cells

design -load before

techmap

clockgate -pos pdk_icg ce:clkin:clkout -tie_lo scanen

# falling edge clock flops don't get matched on -pos
select -module dffe_00 -assert-count 0 t:\\pdk_icg
select -module dffe_01 -assert-count 0 t:\\pdk_icg
# falling edge clock flops do get matched on -pos
select -module dffe_10 -assert-count 1 t:\\pdk_icg
select -module dffe_11 -assert-count 1 t:\\pdk_icg
# if necessary, EN is inverted, since the given ICG
# is assumed to have an active-high EN
select -module dffe_10 -assert-count 1 t:\$_NOT_
select -module dffe_11 -assert-count 0 t:\$_NOT_

# Extra credit: multi-bit FFs work fine as well
select -module dffe_wide_11 -assert-count 1 t:\\pdk_icg

#------------------------------------------------------------------------------

design -load before
clockgate -min_net_size 2 -neg pdk_icg ce:clkin:clkout -tie_lo scanen

# No FF set sharing a (clock, clock enable) pair is large enough
select -module dffe_00 -assert-count 0 t:\\pdk_icg
select -module dffe_01 -assert-count 0 t:\\pdk_icg
select -module dffe_10 -assert-count 0 t:\\pdk_icg
select -module dffe_11 -assert-count 0 t:\\pdk_icg

#------------------------------------------------------------------------------

design -reset
read_rtlil clockgate_bad.il

# Check we don't choke on constants
clockgate -pos pdk_icg ce:clkin:clkout -tie_lo scanen
select -module bad1 -assert-count 0 t:\\pdk_icg
select -module bad2 -assert-count 0 t:\\pdk_icg

#------------------------------------------------------------------------------

# Regression test: EN is a bit from a multi-bit wire
design -reset
read_verilog clockgate_wide.v
yosys proc
opt

clockgate -pos pdk_icg ce:clkin:clkout -tie_lo scanen
select -assert-count 1 t:\\pdk_icg

#------------------------------------------------------------------------------

design -reset
read_liberty c*ckgate.lib
design -save map
foreach mod {dffe_00 dffe_01 dffe_10 dffe_11} {
    design -load before
    hierarchy -top $mod
    read_liberty -lib c*ckgate.lib
    equiv_opt -map %map -multiclock clockgate -liberty c*ckgate.lib
    design -load postopt
    design -copy-to final $mod
}
design -load final

# rising edge ICGs
select -module dffe_00 -assert-count 0 t:\\pos_small
select -module dffe_01 -assert-count 0 t:\\pos_small

select -module dffe_10 -assert-count 1 t:\\pos_small
select -module dffe_11 -assert-count 1 t:\\pos_small

# falling edge ICGs
select -module dffe_00 -assert-count 1 t:\\neg_small
select -module dffe_01 -assert-count 1 t:\\neg_small

select -module dffe_10 -assert-count 0 t:\\neg_small
select -module dffe_11 -assert-count 0 t:\\neg_small

# and nothing else
select -module dffe_00 -assert-count 0 t:\\pos_big
select -module dffe_01 -assert-count 0 t:\\pos_big
select -module dffe_10 -assert-count 0 t:\\pos_big
select -module dffe_11 -assert-count 0 t:\\pos_big
select -module dffe_00 -assert-count 0 t:\\pos_small_tielo
select -module dffe_01 -assert-count 0 t:\\pos_small_tielo
select -module dffe_10 -assert-count 0 t:\\pos_small_tielo
select -module dffe_11 -assert-count 0 t:\\pos_small_tielo
select -module dffe_00 -assert-count 0 t:\\neg_big
select -module dffe_01 -assert-count 0 t:\\neg_big
select -module dffe_10 -assert-count 0 t:\\neg_big
select -module dffe_11 -assert-count 0 t:\\neg_big
select -module dffe_00 -assert-count 0 t:\\neg_small_tielo
select -module dffe_01 -assert-count 0 t:\\neg_small_tielo
select -module dffe_10 -assert-count 0 t:\\neg_small_tielo
select -module dffe_11 -assert-count 0 t:\\neg_small_tielo

# if necessary, EN is inverted, since the given ICG
# is assumed to have an active-high EN
select -module dffe_10 -assert-count 1 t:\$_NOT_
select -module dffe_11 -assert-count 0 t:\$_NOT_

#------------------------------------------------------------------------------

# test multiple liberty files to behave the same way
design -load before
clockgate -liberty clockgate_pos.lib -liberty clockgate_neg.lib

# rising edge ICGs
select -module dffe_00 -assert-count 0 t:\\pos_small
select -module dffe_01 -assert-count 0 t:\\pos_small

select -module dffe_10 -assert-count 1 t:\\pos_small
select -module dffe_11 -assert-count 1 t:\\pos_small

# falling edge ICGs
select -module dffe_00 -assert-count 1 t:\\neg_small
select -module dffe_01 -assert-count 1 t:\\neg_small

select -module dffe_10 -assert-count 0 t:\\neg_small
select -module dffe_11 -assert-count 0 t:\\neg_small

# and nothing else
select -module dffe_00 -assert-count 0 t:\\pos_big
select -module dffe_01 -assert-count 0 t:\\pos_big
select -module dffe_10 -assert-count 0 t:\\pos_big
select -module dffe_11 -assert-count 0 t:\\pos_big
select -module dffe_00 -assert-count 0 t:\\pos_small_tielo
select -module dffe_01 -assert-count 0 t:\\pos_small_tielo
select -module dffe_10 -assert-count 0 t:\\pos_small_tielo
select -module dffe_11 -assert-count 0 t:\\pos_small_tielo
select -module dffe_00 -assert-count 0 t:\\neg_big
select -module dffe_01 -assert-count 0 t:\\neg_big
select -module dffe_10 -assert-count 0 t:\\neg_big
select -module dffe_11 -assert-count 0 t:\\neg_big
select -module dffe_00 -assert-count 0 t:\\neg_small_tielo
select -module dffe_01 -assert-count 0 t:\\neg_small_tielo
select -module dffe_10 -assert-count 0 t:\\neg_small_tielo
select -module dffe_11 -assert-count 0 t:\\neg_small_tielo

# if necessary, EN is inverted, since the given ICG
# is assumed to have an active-high EN
select -module dffe_10 -assert-count 1 t:\$_NOT_
select -module dffe_11 -assert-count 0 t:\$_NOT_

# $sdffe is not gated
select -module sdffe -assert-count 0 sdffe t:* t:\$sdffe %d

#------------------------------------------------------------------------------

design -load before
clockgate -liberty clockgate.lib -dont_use pos_small -dont_use neg_small

# rising edge ICGs
select -module dffe_10 -assert-count 1 t:\\pos_big
select -module dffe_11 -assert-count 1 t:\\pos_big

# falling edge ICGs
select -module dffe_00 -assert-count 1 t:\\neg_big
select -module dffe_01 -assert-count 1 t:\\neg_big

#------------------------------------------------------------------------------

# FFs whose sync reset has priority over the enable

design -reset
read_verilog clockgate_sdffe.v
yosys proc
opt
design -save sdffe_before

# Not transformed without -sdffe
clockgate -pos pdk_icg ce:clkin:clkout -tie_lo scanen
select -module sdffe_pp -assert-count 0 t:\\pdk_icg
select -module sdffce -assert-count 1 t:\\pdk_icg

# The ICG is enabled by CE | SRST and the FF keeps its sync reset
design -load sdffe_before
clockgate -sdffe -pos pdk_icg ce:clkin:clkout -tie_lo scanen
select -module sdffe_pp -assert-count 1 t:\\pdk_icg
select -module sdffe_pp -assert-count 1 t:\$_OR_
select -module sdffe_pp -assert-count 0 t:\$_NOT_
select -module sdffe_pp -assert-count 1 t:\$sdff
select -module sdffe_pp -assert-count 0 t:\$sdffe
# active-low CE and SRST are inverted
select -module sdffe_nn -assert-count 1 t:\\pdk_icg
select -module sdffe_nn -assert-count 2 t:\$_NOT_
# FFs with different resets get different ICGs
select -module sdffe_two_rst -assert-count 2 t:\\pdk_icg
# a reset under the enable needs no OR
select -module sdffce -assert-count 1 t:\\pdk_icg
select -module sdffce -assert-count 0 t:\$_OR_

design -load sdffe_before
clockgate -sdffe -word -pos pdk_icg ce:clkin:clkout -tie_lo scanen
select -module sdffe_nn -assert-count 1 t:\$or
select -module sdffe_nn -assert-count 2 t:\$not

# An FF is disabled only while both CE and SRST are inactive: 0.9 * 0.9 = 0.81
design -load sdffe_before
setattr -set {$DUTY} {"CLK=0.5 EN=0.1 SRST=0.1"} t:\$sdffe
setattr -set {$ACKT} {"CLK=1.0 EN=0.2 SRST=0.2"} t:\$sdffe
design -save sdffe_activity
clockgate -sdffe -min_disabled_threshold 0.85 -pos pdk_icg ce:clkin:clkout -tie_lo scanen
select -module sdffe_pp -assert-count 0 t:\\pdk_icg

design -load sdffe_activity
clockgate -sdffe -min_disabled_threshold 0.8 -pos pdk_icg ce:clkin:clkout -tie_lo scanen
select -module sdffe_pp -assert-count 1 t:\\pdk_icg
select -module sdffe_pp -assert-count 1 t:\\pdk_icg {a:$DUTY=CLK=0.500000 EN=0.190000 SE=0.0 GCLK=0.095000} %i
select -module sdffe_pp -assert-count 1 t:\\pdk_icg {a:$ACKT=CLK=1.000000 EN=0.360000 SE=0.0 GCLK=0.190000} %i
select -module sdffe_pp -assert-count 1 t:\$sdff {a:$DUTY=CLK=0.095000 SRST=0.1} %i

# Fine-grained cells and falling-edge FFs
design -load sdffe_before
techmap
clockgate -sdffe -pos pdk_icg ce:clkin:clkout -neg pdk_icg_neg ce:clkin:clkout
select -module sdffe_nn -assert-count 1 t:\\pdk_icg
select -module sdffe_nn -assert-count 1 t:\$_OR_
select -module sdffe_nn -assert-count 0 t:\$_SDFFE_*
select -module sdffe_nn -assert-count 2 t:\$_SDFF_PN1_ t:\$_SDFF_PN0_ %u
select -module sdffe_neg -assert-count 1 t:\\pdk_icg_neg
select -module sdffe_neg -assert-count 0 t:\\pdk_icg
select -module sdffe_neg -assert-count 2 t:\$_SDFF_NP0_

# The transformed FFs are equivalent, with ICGs that latch their enable
foreach mod {sdffe_pp sdffe_nn sdffe_two_rst sdffce sdffe_neg} {
    foreach fine {0 1} {
        design -load sdffe_before
        hierarchy -top $mod
        if {$fine} { techmap }
        read_verilog -lib clockgate_icg.v
        equiv_opt -assert -map clockgate_icg.v -multiclock clockgate -sdffe \
            -pos pdk_icg ce:clkin:clkout -neg pdk_icg_neg ce:clkin:clkout
    }
}
