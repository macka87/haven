-----------------------------------------------------------------------------
-- Project Name: HAVEN
-- File Name:    wait_unit.vhd
-- Description:  Unit for WAIT commands processing. 
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- Date:         6.4.2011 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity WAIT_UNIT is

   generic
   (
      -- data width
      DATA_WIDTH     : integer := 64;
      DELAY_WIDTH    : integer := 9
   );

   port
   (
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- ----------------- INPUT INTERFACE ----------------------------------
      -- input interface
      DATA           : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IS_WAIT        : in  std_logic;
      IS_CNTR        : in  std_logic;
      CNTR_ZERO      : out std_logic;
            
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      -- output interface
      WAIT_RDY_N     : in  std_logic;
      WAIT_VALUE     : out std_logic_vector(DELAY_WIDTH-1 downto 0);
      WAIT_WR_N      : out std_logic
   );
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of WAIT_UNIT is
-- ==========================================================================
--                                      TYPES
-- ==========================================================================

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================
constant COMP_VALUE : std_logic_vector(DATA_WIDTH-1 downto 0) 
                      := conv_std_logic_vector(255, DATA_WIDTH);
                      
constant ZERO_VALUE : std_logic_vector(DATA_WIDTH-1 downto 0) 
                      := (others => '0');       

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================
signal sig_difference      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_mux_counter     : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_counter_reg     : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_minimum         : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_minimum_final   : std_logic_vector(DELAY_WIDTH-2 downto 0);

-- ==========================================================================
--                           ARCHITECTURE BODY
-- ==========================================================================
begin
   
   mux1 : process (IS_WAIT, sig_difference, DATA)
   begin
      sig_mux_counter <= (others => '0');

      case IS_WAIT is
         when '0'    => sig_mux_counter <= sig_difference;
         when '1'    => sig_mux_counter <= DATA;
         when others => null;   
      end case;   
   end process;
   
   reg1 : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then 
            sig_counter_reg <= (others => '0');
         elsif (((IS_WAIT or IS_CNTR) and (not WAIT_RDY_N)) = '1') then
            sig_counter_reg <= sig_mux_counter;   
         end if;   
      end if;
   end process;
   
   comparator1 : process (sig_mux_counter)
   begin
      if (sig_mux_counter = ZERO_VALUE) then CNTR_ZERO <= '1';
      else CNTR_ZERO <= '0';
      end if;
   end process;
  
   minimum_extractor : process (sig_counter_reg)
   begin
      if (sig_counter_reg > COMP_VALUE) then 
        sig_minimum <= COMP_VALUE;
      else   
        sig_minimum <= sig_counter_reg;
      end if;  
   end process;
   
   sig_difference <= sig_counter_reg - sig_minimum;
   sig_minimum_final <= sig_minimum(DELAY_WIDTH-2 downto 0); 
   
   WAIT_VALUE <= '1' & sig_minimum_final; 
   WAIT_WR_N <= IS_CNTR;
   
end architecture;