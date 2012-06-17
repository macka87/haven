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
   constant clkper            : time := 10 ns; 
   constant reset_time        : time := 100 ns;

   -- signals declarations
   ----------------------------------------------------------------------------
   signal clk                 : std_logic;
   signal reset               : std_logic;
   
   -- UUT signals
   signal unit_part_num       : std_logic_vector(2 downto 0);
   signal unit_part_complete  : std_logic;
   signal unit_last_part      : std_logic;
   
      
-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                   FL_REG_PROC_UNIT
   -- -------------------------------------------------------------------------
   uut: entity work.PART_PROC_UNIT
      port map (
         CLK               => CLK,
         RESET             => RESET,
         
         -- MI32 interface
         PART_NUM          => unit_part_num, 
         PART_COMPLETE     => unit_part_complete,
         LAST_PART         => unit_last_part
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
      unit_part_num      <= "110"; 
      unit_part_complete <= '1'; 
      wait until rising_edge(clk);
      
      wait until (unit_last_part = '1'); 
      
      unit_part_num      <= "111"; 
      unit_part_complete <= '1'; 
      wait until rising_edge(clk); 
      
          
      
      
      wait;
   end process;
end architecture behavioral;
