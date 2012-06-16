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
   constant DATA_WIDTH        : integer := 32;
   
   constant clkper            : time := 10 ns; 
   constant reset_time        : time := 100 ns;

   -- signals declarations
   ----------------------------------------------------------------------------
   signal clk                 : std_logic;
   signal reset               : std_logic;
   
   -- UUT signals
   signal unit_part_size         : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal unit_part_request      : std_logic;
   signal unit_data_size         : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal unit_part_complete     : std_logic;
      
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
         
         -- MI32 interface
         PART_SIZE         => unit_part_size, 
         PART_REQUEST      => unit_part_request,
         DATA_SIZE         => unit_data_size,
         PART_COMPLETE     => unit_part_complete
          
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
      unit_part_request  <= '0';
      unit_part_size     <= X"00000000"; 
      wait until rising_edge(clk);
      
      unit_part_request  <= '1';
      unit_part_size     <= X"00000010";
      wait until rising_edge(clk); 
       
      
      unit_part_size     <= X"00030000"; 
      wait until rising_edge(clk);
       
      
      unit_part_request  <= '1';
      unit_part_size     <= X"00000000";
      
      wait;
   end process;
end architecture behavioral;
