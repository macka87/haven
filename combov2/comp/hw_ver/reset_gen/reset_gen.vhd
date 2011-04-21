--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    Reset generator
-- Description: 
-- Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
-- Date:         15.4.2011 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity RESET_GEN is
   generic
   (
      RESET_TIME     : integer  := 5
   );
   port
   (
      RX_CLK         : in  std_logic;
      RESET          : in  std_logic;

      TX_CLK         : in  std_logic;
      RESET_OUT      : out std_logic
   );
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of RESET_GEN is

constant COUNTER_WIDTH : integer := log2(RESET_TIME);

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================
signal reg_counter          : std_logic_vector(COUNTER_WIDTH-1 downto 0);

signal reset_finished       : std_logic;

begin

   reg_counter_p: process(TX_CLK, RESET)
   begin
      if (RESET = '1') then
         reg_counter <= conv_std_logic_vector(RESET_TIME, COUNTER_WIDTH);
      elsif (rising_edge(TX_CLK)) then
         if (reset_finished = '0') then
            reg_counter <= reg_counter - 1;
         end if;
      end if;
   end process;

   reset_finished_comp: process (reg_counter)
   begin
      reset_finished <= '0';

      if (reg_counter = conv_std_logic_vector(0, COUNTER_WIDTH)) then
         reset_finished <= '1';
      end if;
   end process;

   RESET_OUT <= NOT reset_finished;

end architecture;
