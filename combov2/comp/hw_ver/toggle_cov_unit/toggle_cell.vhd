-----------------------------------------------------------------------------
-- Project Name: HAVEN
-- File Name:    toggle_cell.vhd
-- Description:  Unit for checking toggle coverage of a single signal
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- Date:         6.4.2011 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================

-- This unit serves as a toggle coverage checker for a single signal: it checks
-- whether the value of the signal at DATA_IN was '0' and '1' in the past
-- (since the last RESET of CLEAR signal) and sets the DATA_OUT signal
-- accordingly.
entity toggle_cell is
   port
   (
      -- common signals
      CLK       : in std_logic;
      RESET     : in std_logic;

      -- observed signal (binary, either '0' or '1')
      DATA_IN   : in std_logic;

      -- the enable signal
      EN        : in std_logic;

      -- clear signal
      CLEAR     : in std_logic;

      -- output signal with the following values:
      --  00 : neither 0 nor 1 have been observed
      --  01 : 0 has been observed, 1 not
      --  10 : 1 has been observed, 0 not
      --  11 : both 0 and 1 have been observed
      DATA_OUT  : out std_logic_vector(1 downto 0)
   );
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of toggle_cell is

-- ==========================================================================
--                                      TYPES
-- ==========================================================================

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

   -- inputs
   signal sig_data_in   : std_logic;
   signal sig_en        : std_logic;
   signal sig_clear     : std_logic;

   -- output
   signal sig_data_out  : std_logic_vector(1 downto 0);

   -- the registers maintaining the ``history''
   signal reg_was_zero  : std_logic;
   signal reg_was_one   : std_logic;

begin

   --------------------------------------------------------------------------
   -- inputs
   --------------------------------------------------------------------------
   sig_data_in     <= DATA_IN;
   sig_en          <= EN;
   sig_clear       <= CLEAR;

   --------------------------------------------------------------------------
   -- the registers
   --------------------------------------------------------------------------

   reg_data_p: process(CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            reg_was_zero <= '0';
            reg_was_one  <= '0';
         elsif (sig_clear = '1') then
            reg_was_zero <= NOT sig_data_in;
            reg_was_one  <=     sig_data_in;
         elsif (sig_en = '1') then
            if (sig_data_in = '0') then
               reg_was_zero <= '1';
            elsif (sig_data_in = '1') then
               reg_was_one <= '1';
            end if;
         end if;
      end if;
   end process;

   sig_data_out <= reg_was_one & reg_was_zero;

   --------------------------------------------------------------------------
   -- outputs
   --------------------------------------------------------------------------
   DATA_OUT        <= sig_data_out;


end architecture;
