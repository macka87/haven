--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Adapter
-- Description:  Processes sizes of data parts from FIFO. 
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- Date:         15.6.2013 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity DATA_PROC_UNIT is

   generic
   (
      -- data width
      DATA_WIDTH  : integer := 32
   );

   port
   (
      CLK   : in std_logic;
      RESET : in std_logic;

      -- Input interface
      PART_SIZE     :  in std_logic_vector(DATA_WIDTH-1 downto 0);
      PART_REQUEST  :  in std_logic; 
      
      -- Output interface
      DATA_SIZE     :  out std_logic_vector(DATA_WIDTH-1 downto 0);
      PART_COMPLETE :  out std_logic
    );       
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of DATA_PROC_UNIT is

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================
-- 4KB
constant BLOCK_SIZE : std_logic_vector(DATA_WIDTH-1 downto 0) := X"00010000"; 

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================
signal sig_data_size_reg : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_data_size     : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_cmp_out       : std_logic;
signal sig_output_data   : std_logic_vector(DATA_WIDTH-1 downto 0);

begin

-- register for the data size of a part
   data_size_reg_p: process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            sig_data_size_reg <= (others => '0');
         elsif (PART_REQUEST = '1') then
            sig_data_size_reg <= sig_data_size; 
         end if;
      end if;
   end process; 
   
-- data size mux
   data_size_mux : process (PART_SIZE, sig_data_size_reg, sig_cmp_out)
   begin
      sig_data_size <= (others => '0');

      case sig_cmp_out is
         when '0'    => sig_data_size <= PART_SIZE;
         when '1'    => sig_data_size <= sig_data_size_reg - BLOCK_SIZE;
         when others => null;   
      end case;
   end process;   
   
-- data size comparator
   data_size_cmp : process (sig_data_size_reg)
   begin
      sig_cmp_out <= '0';

      if (sig_data_size_reg >= BLOCK_SIZE) then sig_cmp_out <= '1';
      else sig_cmp_out <= '0';
      end if;
   end process;  
   
-- output data mux
   output_data_mux : process (sig_data_size_reg, sig_cmp_out)
   begin
      sig_output_data <= (others => '0');

      case sig_cmp_out is
         when '0'    => sig_output_data <= sig_data_size_reg;
         when '1'    => sig_output_data <= BLOCK_SIZE;
         when others => null;   
      end case;
   end process; 
   
   DATA_SIZE     <= sig_output_data;
   PART_COMPLETE <= not sig_cmp_out;
     
end architecture;
