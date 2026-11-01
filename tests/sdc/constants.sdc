create_clock -name clk -period 1.0
create_clock -name clk2 -period 2.0
set_clock_groups -asynchronous -group "[get_clocks clk] [get_clocks clk2]"
set_input_delay 0.1 -clock clk [get_ports {a b}]
set_logic_one [get_ports { en }]
set_logic_one [get_ports {z}]
set_logic_zero [get_clocks clk]
source $FORCES_DIR/constants_forces.sdc
