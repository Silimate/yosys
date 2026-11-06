entity old87 is
  port (a, b : in integer range 0 to 15;
        y : out integer range 0 to 30;
        n : out integer);
end old87;

architecture rtl of old87 is
begin
  y <= a + b;
  n <= a;
end rtl;
