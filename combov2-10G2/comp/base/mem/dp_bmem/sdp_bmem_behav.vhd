-- sdp_bmem_behav.vhd: Half dual port generic BlockRAM memory (behavioral)
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Puš <puš@liberouter.org>
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
use WORK.bmem_func.all;

-- pragma translate_off
library UNISIM;
use UNISIM.vcomponents.all;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of SDP_BMEM is
    
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

   shared variable memory : t_mem := BRAM_INIT_MEM;
   
   signal dob_to_reg        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_dob           : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_dob_dv1       : std_logic;
   signal reg_dob_dv2       : std_logic;

   attribute ram_style of memory: variable is "block"; -- auto,block,distributed
   attribute block_ram of memory: variable is true; -- true,false
   
begin
   
   -- ------------------------- memory - port A ------------------------------
   
   process(CLKA)
   begin
      if (CLKA'event and CLKA = '1') then
         if (WEA = '1') then
            memory(conv_integer(unsigned(ADDRA))) := DIA;
         end if;
      end if;
   end process;
   
   
   -- ------------------------- memory - port B ------------------------------
   
   process(CLKB)
   begin
      if (CLKB'event and CLKB = '1') then
         if (PIPE_ENB = '1') then
            dob_to_reg <= memory(conv_integer(unsigned(ADDRB)));
         end if;
      end if;
   end process;
   
   -- ------------------------ Output registers -------------------------------
   OUTPUTREG : if (OUTPUT_REG = true or OUTPUT_REG = auto) generate
      -- DOB Register
      process(RESET, CLKB)
      begin
         if (RESET = '1') then
            reg_dob     <= (others => '0');
            reg_dob_dv1 <= '0';
            reg_dob_dv2 <= '0';
         elsif (CLKB'event AND CLKB = '1') then
            if (PIPE_ENB = '1') then
              reg_dob     <= dob_to_reg;
              reg_dob_dv1 <= REB;
              reg_dob_dv2 <= reg_dob_dv1;
            end if;
         end if;
      end process;
   
      -- mapping registers to output
      DOB <= reg_dob;
      DOB_DV <= reg_dob_dv2;
   end generate;


   -- --------------------- No Output registers -------------------------------
   NOOUTPUTREG : if (OUTPUT_REG = false) generate
   
      process(RESET, CLKB)
      begin
         if (RESET = '1') then
            DOB_DV <= '0';
         elsif (CLKB'event AND CLKB = '1') then
            if (PIPE_ENB = '1') then
               DOB_DV <= REB;
            end if;
         end if;
      end process;
      
      -- mapping memory to output
      DOB <= dob_to_reg;
   end generate;
   
end architecture behavioral;
