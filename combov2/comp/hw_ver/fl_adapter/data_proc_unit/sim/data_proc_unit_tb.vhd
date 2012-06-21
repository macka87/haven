-- Copyright (C) 2012 
-- Author(s): Marcela Simkova <isimkova@fit.vutbr.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   -- constants declarations
   ----------------------------------------------------------------------------
   constant SIZE_WIDTH        : integer := 32;
   constant DATA_WIDTH        : integer := 64;
   
   constant clkper            : time := 10 ns; 
   constant reset_time        : time := 100 ns;

   -- signals declarations
   ----------------------------------------------------------------------------
   signal clk                 : std_logic;
   signal reset               : std_logic;
   
   -- UUT signals
   signal unit_part_size_request : std_logic;
   signal unit_data_size         : std_logic_vector(SIZE_WIDTH-1 downto 0);
   signal unit_data_request      : std_logic;
   signal unit_data_complete     : std_logic;
   signal unit_data_rem          : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      
-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                   FL_REG_PROC_UNIT
   -- -------------------------------------------------------------------------
   uut: entity work.DATA_PROC_UNIT
      generic map (
         DATA_WIDTH        => DATA_WIDTH
      )
      port map (
         CLK               => CLK,
         RESET             => RESET,
         
         -- interface
         DATA_SIZE          => unit_data_size,
      
         -- Data processing interface
         DATA_REQUEST  => unit_data_request,
         DATA_COMPLETE => unit_data_complete,
         DATA_REM      => unit_data_rem
          
      );

   -- ----------------------------------------------------

   -- CLK generator
   clkgen: process
   begin
      clk <= '1';
      wait for clkper/2;
      clk <= '0';
      wait for clkper/2;
   end process;
   
   resetgen: process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process;

   tb: process

   begin
   
      wait for reset_time; 
      wait until rising_edge(clk);
   
      -- initialization 
      unit_data_size    <=  X"00000000";
      unit_data_request <= '0';
      wait until rising_edge(clk);
      
      unit_data_size    <=  X"00000020";
      unit_data_request <= '1';
      wait until rising_edge(clk); 
      wait until (unit_data_complete = '1');
       
      unit_data_size    <=  X"00000082"; 
      wait until rising_edge(clk);
       
      
      unit_data_size     <= X"00000000";
      
      wait;
   end process;
end architecture behavioral;
