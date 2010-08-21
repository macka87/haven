--
-- dp_bmem_behav.vhd: Single port generic BlockRAM memory (behavioral)
-- Copyright (C) 2008 CESNET
-- Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions
-- are met:
-- 1. Redistributions of source code must retain the above copyright
--    notice, this list of conditions and the following disclaimer.
-- 2. Redistributions in binary form must reproduce the above copyright
--    notice, this list of conditions and the following disclaimer in
--    the documentation and/or other materials provided with the
--    distribution.
-- 3. Neither the name of the Company nor the names of its contributors
--    may be used to endorse or promote products derived from this
--    software without specific prior written permission.
--
-- This software is provided ``as is'', and any express or implied
-- warranties, including, but not limited to, the implied warranties of
-- merchantability and fitness for a particular purpose are disclaimed.
-- In no event shall the company or contributors be liable for any
-- direct, indirect, incidental, special, exemplary, or consequential
-- damages (including, but not limited to, procurement of substitute
-- goods or services; loss of use, data, or profits; or business
-- interruption) however caused and on any theory of liability, whether
-- in contract, strict liability, or tort (including negligence or
-- otherwise) arising in any way out of the use of this software, even
-- if advised of the possibility of such damage.
--
-- $Id$
--
-- TODO:


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
-- auxilarity functions and constant needed to evaluate generic address etc.
use WORK.math_pack.all;

-- pragma translate_off
library UNISIM;
use UNISIM.vcomponents.all;
-- pragma translate_on



-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of SP_BMEM is
   
   attribute ram_style   : string; -- for XST
   attribute block_ram   : boolean; -- for precision
   
   type t_mem is array(0 to ITEMS-1) of std_logic_vector(DATA_WIDTH-1 downto 0);
   
   -- ----------------------------------------------------------------------
   -- Function to Zero out the memory
   -- This is to prevent 'U' signals in simulations
   function BRAM_INIT_MEM return t_mem is
      variable init : t_mem;
   begin
      for i in 0 to ITEMS - 1 loop
         init(i) := (others => '0');
      end loop;

      return init;
   end BRAM_INIT_MEM;
   -- ----------------------------------------------------------------------
   
   signal memory : t_mem;
   
   attribute ram_style of memory: signal is "block"; -- auto,block,distributed
   attribute block_ram of memory: signal is true; -- true,false
   
   signal do_to_reg        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_do           : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_do_dv1       : std_logic;
   signal reg_do_dv2       : std_logic;
   
begin
   
   -- ------------------------------ memory -----------------------------------
   
   process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (PIPE_EN = '1') then
            if (WE = '1') then
               memory(conv_integer(unsigned(ADDR))) <= DI;
            end if;
            do_to_reg <= memory(conv_integer(unsigned(ADDR)));
         end if;
      end if;
   end process;
   
   
   -- ------------------------ Output registers -------------------------------
   OUTPUTREG : if (OUTPUT_REG = true or OUTPUT_REG = auto) generate
      -- DO Register
      process(RESET, CLK)
      begin
         if (RESET = '1') then
            reg_do     <= (others => '0');
            reg_do_dv1 <= '0';
            reg_do_dv2 <= '0';
         elsif (CLK'event AND CLK = '1') then
            if (PIPE_EN = '1') then
               reg_do     <= do_to_reg;
               reg_do_dv1 <= RE;
               reg_do_dv2 <= reg_do_dv1;
            end if;
         end if;
      end process;
   
      -- mapping registers to output
      DO <= reg_do;
      DO_DV <= reg_do_dv2;
   end generate;


   -- --------------------- No Output registers -------------------------------
   NOOUTPUTREG : if (OUTPUT_REG = false) generate
      process(RESET, CLK)
      begin
         if (RESET = '1') then
            DO_DV <= '0';
         elsif (CLK'event AND CLK = '1') then
            if (PIPE_EN = '1') then
               DO_DV <= RE;
            end if;
         end if;
      end process;
      
      -- mapping memory to output
      DO <= do_to_reg;
   end generate;
   
end architecture behavioral;
