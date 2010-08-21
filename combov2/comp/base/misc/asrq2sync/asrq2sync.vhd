-- asrq2sync.vhd: This component transform leading edge of asynchronous
--		  signal to one puls of synchronous one. Instead of leading
--		  edge could be used clock from asynchronous signal
--		  with conjuction of enable signal as well.
--		  Beware design use async reset, so be carefull with using it.
--
-- Copyright (C) 2004 Masaryk University
-- Author(s): Jiri Novotny <novotny@ics.muni.cz>
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

-- ----------------------------------------------------------------------------
--                      Entity declaration
-- ----------------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;

entity ASRQ2SYNC is
   port (
      -- Input
      ASY_PE	: in std_logic; -- pulse enable
      ASY_CLK	: in std_logic; -- clock from asynchronous signal
      SYNC_CLK	: in std_logic; -- clock from synchrnous signal
      RESET	: in std_logic; -- main reset

      -- Output
      SYNC_PULS	: out std_logic -- otput of pulse synchronous with sync clock
   );
end ASRQ2SYNC;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of asrq2sync is

   signal asy_res	: std_logic;
   signal asy_out	: std_logic;

begin

   process (ASY_CLK, asy_res, RESET)
   begin
      if asy_res = '1' or RESET = '1' then
         asy_out <= '0';
      elsif (ASY_CLK'event and ASY_CLK = '1') then
         asy_out <= ASY_PE;
      end if;
   end process;

   process (SYNC_CLK, RESET)
   begin
      if RESET = '1' then
         asy_res <= '0';
      elsif (SYNC_CLK'event and SYNC_CLK = '1') then
         asy_res <= asy_out;
      end if;
   end process;

   SYNC_PULS <= asy_res;

end behavioral;



