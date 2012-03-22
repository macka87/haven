-----------------------------------------------------------------------------
-- Project Name: HAVEN
-- File Name:    multiplier.vhd
-- Description:  Booth's Multiplier Unit
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- Date:         14.3.2012 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity MULT is
   generic
   (
      DATA_WIDTH  : integer := 8       
   );

   port
   (
      CLK         : in  std_logic;
      RST         : in  std_logic;
      
      -- ----------------- INPUT INTERFACE ----------------------------------
      INPUT_A     : in  std_logic_vector(DATA_WIDTH-1 downto 0); -- register A
      INPUT_B     : in  std_logic_vector(DATA_WIDTH-1 downto 0); -- register B 
      START       : in std_logic; 
           
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      MULT_RESULT : out std_logic_vector(2*DATA_WIDTH-1 downto 0);
      MULT_VLD    : out std_logic
   );
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture MULT_ARCH of MULT is

-- ==========================================================================
--                                      TYPES
-- ==========================================================================

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================
-- counter signals
signal sig_counter         : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_mult_finish     : std_logic;

-- signals for operand A processing
signal sig_shift_operand_A : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_reg_operand_A   : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_reg_exp_A       : std_logic_vector((DATA_WIDTH*2)-1 downto 0);

-- signals for operand B processing
signal sig_shift_operand_B : std_logic_vector((DATA_WIDTH*2)-1 downto 0);
signal sig_reg_operand_B   : std_logic_vector((DATA_WIDTH*2)-1 downto 0);

-- result
signal sig_add_result      : std_logic_vector((DATA_WIDTH*2)-1 downto 0);
signal sig_and_result      : std_logic_vector((DATA_WIDTH*2)-1 downto 0);
signal sig_reg_result      : std_logic_vector((DATA_WIDTH*2)-1 downto 0);

begin

-- counter
   counter: process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RST ='1' or START = '1') then
            sig_counter <= (others => '0');
         else sig_counter <= sig_counter + 1;
         end if;
      end if;   
   end process;
   
   sig_mult_finish <= '1' when sig_counter = (DATA_WIDTH-1) else '0';

-- register for operand A
   reg1 : process (CLK)
   begin          
      if (rising_edge(CLK)) then
         if (RST = '1') then
            sig_reg_operand_A <= (others => '0');
         elsif (START = '1') then 
            sig_reg_operand_A <= INPUT_A;
         elsif (START = '0') then
            sig_reg_operand_A <= sig_shift_operand_A;
         end if;   
      end if;
   end process;
   
-- expansion of register operand  
   shift : process (sig_reg_operand_A)
   begin
      if (sig_reg_operand_A(0) = '0') then sig_reg_exp_A <= (others => '0');
      else sig_reg_exp_A <= (others => '1'); 
      end if;
   end process;       
   
-- register for operand B
   reg2 : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RST = '1') then
            sig_reg_operand_B <= (others => '0');
         elsif (START = '1') then 
            sig_reg_operand_B(DATA_WIDTH-1 downto 0) <= INPUT_B;
            sig_reg_operand_B(2*DATA_WIDTH-1 downto DATA_WIDTH) <= (others => '0');
         elsif (START = '0') then
            sig_reg_operand_B <= sig_shift_operand_B;
         end if;   
      end if;
   end process;    
   
-- AND 
   sig_and_result <= sig_reg_exp_A and sig_reg_operand_B;   
   
-- shift right for operand A
   sig_shift_operand_A <= '0' & sig_reg_operand_A(DATA_WIDTH-1 downto 1);
   
-- shift left for operand B
   sig_shift_operand_B <= sig_reg_operand_B((DATA_WIDTH*2-2) downto 0) & '0';
   
-- adder
   sig_add_result <= sig_and_result + sig_reg_result;
   
-- register for result
   reg3 : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RST ='1' or START = '1') then
            sig_reg_result <= (others => '0');
         else sig_reg_result <= sig_add_result;
         end if;   
      end if;
   end process;  
   
   MULT_RESULT <= sig_add_result;  -- or sig_reg_result but 1 tact more for mult
   MULT_VLD    <= sig_mult_finish;
   
end architecture;
