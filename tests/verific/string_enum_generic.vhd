-- Enumeration generics that a Verilog instance sets with string actuals, for string_enum_generic*.ys
package string_enum_generic_pkg is
  type state_t is (IDLE, RUN, DONE);
  subtype early_t is state_t range IDLE to RUN;
end package;

use work.string_enum_generic_pkg.all;

entity flags is
  generic (
    A : boolean := true;
    B : boolean := false;
    S : state_t := IDLE
  );
  port (
    a_o : out bit;
    b_o : out bit;
    s_o : out bit_vector(1 downto 0)
  );
end entity;

architecture rtl of flags is
begin
  -- A boolean generic that picks a generate branch, as in the ascal scaler
  a_on : if A generate
    a_o <= '1';
  end generate;
  a_off : if not A generate
    a_o <= '0';
  end generate;
  b_o <= '1' when B else '0';
  s_o <= "00" when S = IDLE else "01" when S = RUN else "10";
end architecture;

use work.string_enum_generic_pkg.all;

entity early is
  generic (E : early_t := IDLE);
  port (o : out bit);
end entity;

architecture rtl of early is
begin
  o <= '1' when E = RUN else '0';
end architecture;
