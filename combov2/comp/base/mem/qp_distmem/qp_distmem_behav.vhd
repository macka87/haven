-- qp_distmem_behav.vhd: Generic quad-port distributed memory (behavioral)
-- Copyright (C) 2010 CESNET
-- Author(s): Jakub Sochor <xsocho06@stud.fit.vutbr.cz>
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
-- library with log2 function
use WORK.math_pack.all;

-- pragma translate_off
library UNISIM;
use UNISIM.vcomponents.all;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of QP_DISTMEM is

   attribute ram_style   : string; -- for XST
   attribute block_ram   : boolean; -- for precision
   

   type t_mem is array(0 to ITEMS-1) of std_logic_vector(DATA_WIDTH-1 downto 0);

   signal gndvec : std_logic_vector(DATA_WIDTH-1 downto 0) := (others => '0');

   function mem_init(INIT_DATA : in std_logic_vector) return t_mem is
   variable ra : t_mem;
   begin
      for i in 0 to ITEMS - 1 loop
         ra(i) := INIT_DATA;
      end loop;
   return ra;
   end;

   signal memory : t_mem 
-- pragma translate_off
   := mem_init(gndvec)
-- pragma translate_on
   ;
   
   attribute ram_style of memory: signal is "distributed"; -- auto,block,distributed
   attribute block_ram of memory: signal is false;         -- true,false 
   
begin
   
   -- ------------------------- quad-port memory ------------------------------
   process(WCLK)
   begin
      if (WCLK'event and WCLK = '1') then
         if (WE = '1') then
            memory(conv_integer(unsigned(ADDRA))) <= DI;
         end if;
      end if;
   end process;

   DOA <= memory(conv_integer(unsigned(ADDRA)));   
   DOB <= memory(conv_integer(unsigned(ADDRB)));
   DOC <= memory(conv_integer(unsigned(ADDRC)));
   DOD <= memory(conv_integer(unsigned(ADDRD)));
   
end architecture behavioral;
