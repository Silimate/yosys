#!/usr/bin/env bash
# verific -f reads a file list entry as VHDL when its extension is .vhd, .vhdl or .vho (a VHDL
# netlist), in any case. Anything else is Verilog, including a name without a dot, such as vhd.
set -euo pipefail
YOSYS=$(realpath "$(command -v "${YOSYS:-../../build/yosys}")")
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
# The file list names bare files, so that vhd is a whole path with no dot in it
cd "$tmp"

cat > EXT_PKG.VHD <<'EOT'
library ieee;
use ieee.std_logic_1164.all;

package ext_pkg is
	constant EXT_WIDTH : natural := 4;
end package ext_pkg;
EOT

cat > ext_net.vho <<'EOT'
-- Vendor tools write VHDL netlists with the .vho extension
library ieee;
use ieee.std_logic_1164.all;

entity ext_net is
	port (a : in std_logic; y : out std_logic);
end entity ext_net;

architecture structure of ext_net is
begin
	y <= not a;
end architecture structure;
EOT

cat > EXT_TOP.Vhdl <<'EOT'
library ieee;
use ieee.std_logic_1164.all;
use work.ext_pkg.all;

entity ext_top is
	port (
		a : in std_logic_vector(EXT_WIDTH - 1 downto 0);
		y : out std_logic_vector(EXT_WIDTH - 1 downto 0)
	);
end entity ext_top;

architecture rtl of ext_top is
begin
	g : for i in 0 to EXT_WIDTH - 1 generate
		u : entity work.ext_net port map (a => a(i), y => y(i));
	end generate;
end architecture rtl;
EOT

cat > vhd <<'EOT'
module noext(input a, output y);
	assign y = a;
endmodule
EOT

printf '%s\n' EXT_PKG.VHD ext_net.vho EXT_TOP.Vhdl vhd > list.f

# Read as Verilog, EXT_PKG.VHD and ext_net.vho fail to analyze; read as VHDL, vhd does.
# The entity instance imports as ext_net(structure), after its architecture.
$YOSYS -q -p "verific -f list.f; verific -import ext_top noext; select -assert-mod-count 3 ext_top ext_net* noext; select -assert-count 4 ext_top/t:ext_net*"
