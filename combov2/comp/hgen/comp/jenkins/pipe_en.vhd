-- pipe_en.vhd: Simple logic for single cycle pipeline part enabling
-- Copyright (C) 2008 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use IEEE.numeric_std.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity pipe_en is
   generic(
      RESET_STATE : std_logic := '0'
   );
   port(
      CLK      : in  std_logic;
      RESET    : in  std_logic;

      IN_RDY   : in  std_logic;
      IN_NEXT  : out std_logic;

      OUT_RDY  : out std_logic;
      OUT_NEXT : in  std_logic;

      EN       : out std_logic
   );
end entity pipe_en;


-- ----------------------------------------------------------------------------
--                        Architecture description
-- ----------------------------------------------------------------------------
architecture full of pipe_en is

   signal reg_rdy    : std_logic;
   signal want_next  : std_logic;
   signal sig_en     : std_logic;

begin

   -- Combinational logic
   want_next   <= OUT_NEXT or not reg_rdy;
   sig_en      <= IN_RDY and want_next;

   reg_rdy_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            reg_rdy <= RESET_STATE;
         else
            if want_next = '1' then
               reg_rdy <= sig_en;
            end if;
         end if;
      end if;
   end process;

   OUT_RDY <= reg_rdy;
   IN_NEXT <= want_next;
   EN      <= sig_en;

end architecture full;
