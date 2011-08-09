library ieee;
use ieee.std_logic_1164.all;

entity testbench is
end entity testbench;

architecture tb_arch of testbench is
  -- perioda hodin 
  constant clk_period   : time    := 20 ns;
  -- prepajacie signaly
  signal clk      : std_logic;
  signal reset    : std_logic;
  signal seed     : std_logic_vector(7 downto 0);
  signal en       : std_logic;
  signal output   : std_logic;
  
begin
  -- instancia testovanej komponenty
  UUT : entity work.PRNG_8
  port map( CLK     => clk,
            RESET   => reset,
            SEED    => seed,
            EN      => en,
            OUTPUT  => output
  );

  -- generovanie hodinoveho signalu 
  clk_gen :  process 
  begin  
    clk <='1';
    wait for clk_period/2;
    clk <='0';
    wait for clk_period/2;
  end process clk_gen;

  -- generovanie vstupov
  behaviour : process
  begin
    -- pociatocne hodnoty vstupov
    reset <= '1';
    seed  <= "10011011";
            
    -- test 
    wait for 2*clk_period;
    reset <= '0';
            
    -- test 
    wait for 60*clk_period;
  end process behaviour; 
   
end architecture tb_arch;
