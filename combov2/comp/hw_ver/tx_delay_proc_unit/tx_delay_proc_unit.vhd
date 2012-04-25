-- --------------------------------------------------------------------------
-- Project Name: HAVEN
-- File Name:    tx_delay_proc_unit.vhd  
-- Description:  TX Delay Processing Unit
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- Date:         19.4.2012 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity TX_DELAY_PROC_UNIT is

   generic
   (
      -- delay width
      DELAY_WIDTH    : integer := 9
   );

   port
   (
      CLK            : in  std_logic;
      RESET          : in  std_logic;
      DELAY_DATA     : in  std_logic_vector(DELAY_WIDTH-1 downto 0);
      DELAY_READ     : out std_logic;
      DELAY_EMPTY    : in  std_logic;
      DST_RDY        : in  std_logic;
      SRC_RDY        : out std_logic
   );
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of TX_DELAY_PROC_UNIT is
-- ==========================================================================
--                                      TYPES
-- ==========================================================================


-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================


-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- delay signals
signal sig_is_wait          : std_logic; 
signal sig_drive_mx         : std_logic;
signal sig_reg_is_wait      : std_logic; 
signal sig_mux_is_wait      : std_logic; 
signal sig_mux_delay_data   : std_logic_vector(DELAY_WIDTH-2 downto 0);
signal sig_decremented      : std_logic_vector(DELAY_WIDTH-2 downto 0);
signal sig_delay            : std_logic_vector(DELAY_WIDTH-2 downto 0);
signal sig_delay_data       : std_logic_vector(DELAY_WIDTH-2 downto 0);
signal sig_reg_delay        : std_logic_vector(DELAY_WIDTH-2 downto 0);
signal sig_take             : std_logic;
signal sig_comp_output      : std_logic;
signal sig_reg_reset        : std_logic;
signal sig_taken_or         : std_logic;
signal sig_taken            : std_logic;

-- ==========================================================================
--                           ARCHITECTURE BODY
-- ==========================================================================
begin

   sig_is_wait    <= DELAY_DATA(DELAY_WIDTH-1); -- delay (0), wait (1)
   sig_delay_data <= DELAY_DATA(DELAY_WIDTH-2 downto 0);

   -- multiplexer
   mux0 : process (sig_is_wait, sig_delay_data)
   begin
      sig_mux_delay_data <= sig_delay_data;

      case sig_is_wait is
         when '0'    => sig_mux_delay_data <= sig_delay_data;
         when '1'    => sig_mux_delay_data <= sig_delay_data-1;
         when others => null;   
      end case;   
   end process;

   -- register for sig_is_wait 
   reg1 : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (sig_take = '1') then
            sig_reg_is_wait <= sig_is_wait OR DELAY_EMPTY;   
         end if;   
      end if;
   end process;
   
   sig_drive_mx <= sig_take and sig_comp_output;
   
   -- multiplexer
   mux1 : process (sig_drive_mx, sig_is_wait, sig_reg_is_wait)
   begin
      sig_mux_is_wait <= '0';

      case sig_drive_mx is
         when '0'    => sig_mux_is_wait <= sig_reg_is_wait;
         when '1'    => sig_mux_is_wait <= sig_is_wait;
         when others => null;   
      end case;   
   end process;
   
   -- multiplexer
   mux2 : process (sig_take, sig_mux_delay_data, sig_decremented)
   begin
      sig_delay <= sig_decremented;

      case sig_take is
         when '0'    => sig_delay <= sig_decremented;
         when '1'    => sig_delay <= sig_mux_delay_data;
         when others => null;   
      end case;   
   end process;
   
   -- comparator
   comp : process (sig_delay)
   begin
     if (sig_delay = 0) then sig_comp_output <= '1';
     else sig_comp_output <= '0'; 
     end if;
   end process;
   
   -- register for decrement 
   reg2 : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (sig_comp_output = '0') then
            sig_reg_delay <= sig_delay;   
         end if;   
      end if;
   end process;
   
   sig_decremented <= sig_reg_delay - 1;
   
   sig_taken <= (sig_comp_output and DST_RDY) or (sig_comp_output and sig_mux_is_wait);
   
   -- register for reset
   reg3 : process (CLK, RESET)
   begin
      if (RESET = '1') then 
         sig_reg_reset <= '1';
      elsif (rising_edge(CLK)) then
         if (sig_reg_reset = '1') then
            sig_reg_reset <= '0';  
         end if;   
      end if;
   end process;
   
   sig_taken_or <= sig_taken or sig_reg_reset; 
   
   -- register for taken
   reg4 : process (CLK, RESET)
   begin
      if (RESET = '1') then 
         sig_take <= '0'; 
      elsif (rising_edge(CLK)) then
         if (sig_taken_or = '1') then
            sig_take <= sig_taken_or;     
         elsif (sig_take = '1') then
            sig_take <= '0';   
         end if;   
      end if;
   end process;
   
   SRC_RDY <= ((not sig_mux_is_wait) and sig_comp_output) AND (NOT(DELAY_EMPTY and sig_take));
   DELAY_READ  <= sig_take and (not DELAY_EMPTY);

end architecture;
