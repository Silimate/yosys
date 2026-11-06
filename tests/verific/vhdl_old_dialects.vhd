library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity old93 is
  port (a, b : in std_logic_vector(3 downto 0);
        y : out std_logic_vector(3 downto 0);
        n : out integer);
end old93;

architecture rtl of old93 is
begin
  y <= std_logic_vector(unsigned(a) + unsigned(b));
  n <= to_integer(unsigned(a));
end rtl;
