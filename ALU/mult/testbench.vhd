library ieee;
use ieee.std_logic_1164.all;

entity testbench is
end entity testbench;

architecture tb_arch of testbench is
  -- perioda hodin 
  constant clk_period   : time := 20 ns;
  constant reset_time   : time := 100 ns;
  constant data_width   : integer := 8;
  
  -- prepajacie signaly
  signal clk         : std_logic;
  signal rst         : std_logic;
  signal input_a     : std_logic_vector(data_width-1 downto 0);
  signal input_b     : std_logic_vector(data_width-1 downto 0);
  signal start       : std_logic;
  signal mult_result : std_logic_vector(data_width*2-1 downto 0);
  signal mult_vld    : std_logic;
  
begin
  -- instancia testovanej komponenty
  UUT : entity work.MULT
  port map( CLK         => clk,
            RST         => rst,
            INPUT_A     => input_a,
            INPUT_B     => input_b,
            START       => start,
            MULT_RESULT => mult_result, 
            MULT_VLD    => mult_vld
  );

  -- generovanie hodinoveho signalu 
  clk_gen :  process 
  begin  
    clk <='1';
    wait for clk_period/2;
    clk <='0';
    wait for clk_period/2;
  end process clk_gen;
  
  resetgen: process
   begin
      rst <= '1';
      wait for reset_time;
      rst <= '0';
      wait;
   end process;

  -- generovanie vstupov
  behaviour : process
  begin
    
    start    <= '0';
    input_a  <= "00000000";
    input_b  <= "00000000";
    
    wait for 8*clk_period;
    
    -- pociatocne hodnoty vstupov
    input_a  <= "11111111";
    input_b  <= "11111111";
    start    <= '1';
    
    wait for clk_period;
    start    <= '0';  
    
    wait for 10*clk_period;
    
    -- pociatocne hodnoty vstupov
    input_a  <= "00000101";
    input_b  <= "00000100";
    start    <= '1';     
    
    wait for clk_period;
    start    <= '0'; 
    
    wait until (mult_vld = '1');            
    wait;
  end process behaviour; 
   
end architecture tb_arch;
