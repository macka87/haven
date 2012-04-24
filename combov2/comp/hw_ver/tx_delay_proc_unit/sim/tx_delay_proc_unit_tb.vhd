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
   constant DELAY_WIDTH       : integer := 9;

   constant clkper            : time := 10 ns; 
   constant reset_time        : time := 105 ns;

   -- signals declarations
   ----------------------------------------------------------------------------
   signal clk                 : std_logic;
   signal reset               : std_logic;
   
   -- UUT input signals
   signal sig_delay_data      : std_logic_vector(DELAY_WIDTH-1 downto 0);
   signal sig_delay_read      : std_logic;
   signal sig_delay_empty     : std_logic;
   signal sig_dst_rdy         : std_logic;
   signal sig_src_rdy         : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                   FL Shortener
   -- -------------------------------------------------------------------------
   uut: entity work.TX_DELAY_PROC_UNIT
      generic map (
         DELAY_WIDTH       => DELAY_WIDTH
      )
      port map (
         CLK               => clk,
         RESET             => reset,
         DELAY_DATA        => sig_delay_data,
         DELAY_READ        => sig_delay_read,
         DELAY_EMPTY       => sig_delay_empty,
         DST_RDY           => sig_dst_rdy,
         SRC_RDY           => sig_src_rdy
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
      
      sig_delay_data  <= "0" & X"02";  -- 0 & 2  DELAY
      sig_delay_empty <= '0';
      sig_dst_rdy     <= '1';
      
      wait for 5*clkper;
       
      sig_delay_data  <= "1" & X"05";  -- 1 & 2  WAIT
      sig_delay_empty <= '0';
      sig_dst_rdy     <= '1';

      wait for 5*clkper;
      sig_delay_data  <= "0" & X"02";  -- 0 & 2  DELAY
      sig_delay_empty <= '0';
      sig_dst_rdy     <= '1';
      
      wait for 5*clkper;
       
      sig_delay_data  <= "1" & X"01";  -- 1 & 2  WAIT
      sig_delay_empty <= '0';
      sig_dst_rdy     <= '1';

      wait for 5*clkper;
      sig_delay_data  <= "0" & X"00";  -- 0 & 2  DELAY
      sig_delay_empty <= '0';
      sig_dst_rdy     <= '1';

      wait;
   end process;
end architecture behavioral;
