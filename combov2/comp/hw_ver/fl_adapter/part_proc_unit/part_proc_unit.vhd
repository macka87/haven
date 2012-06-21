--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Adapter
-- Description:  Part processing unit. 
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- Date:         17.6.2013 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;         
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity PART_PROC_UNIT is

   port
   (
      CLK   : in std_logic;
      RESET : in std_logic;

      -- Input interface
      PART_NUM      :  in  std_logic_vector(2 downto 0);
      PART_COMPLETE :  in  std_logic; 
      
      -- Output interface
      LAST_PART     :  out std_logic
    );       
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of PART_PROC_UNIT is

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================


-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================
signal sig_parts_reg   : std_logic_vector(2 downto 0);
signal sig_counter_reg : std_logic_vector(2 downto 0);
signal sig_counter     : std_logic_vector(2 downto 0);
signal sig_cmp_out     : std_logic;
signal sig_cmp_reg     : std_logic;

begin

-- register for parts
   parts_reg_p: process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            sig_parts_reg <= (others => '0');
         elsif (sig_cmp_reg = '1') then
            sig_parts_reg <= PART_NUM; 
         end if;
      end if;
   end process; 
   
-- register for counter
   counter_reg_p: process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            sig_counter_reg <= (others => '0');
         elsif (PART_COMPLETE = '1') then
            sig_counter_reg <= sig_counter; 
         end if;
      end if;
   end process;    
   
-- counter mux
   counter_mux : process (sig_counter_reg, sig_cmp_out)
   begin
      sig_counter <= (others => '0');

      case sig_cmp_out is
         when '0'    => sig_counter <= sig_counter_reg + 1;
         when '1'    => sig_counter <= "000";
         when others => null;   
      end case;
   end process;   
   
-- parts comparator
   parts_cmp : process (sig_parts_reg, sig_counter_reg)
   begin
      sig_cmp_out <= '1';

      if (sig_parts_reg = sig_counter_reg) then sig_cmp_out <= '1';
      else sig_cmp_out <= '0';
      end if;
   end process; 
   
   LAST_PART <= sig_cmp_out; 
   
-- register for comparator output
   cmp_reg_p: process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            sig_cmp_reg <= '0';
         elsif (PART_COMPLETE = '1') then
            sig_cmp_reg <= sig_cmp_out; 
         end if;
      end if;
   end process;    
   
end architecture;
