
-- tx_buf_fsm.vhd: TX buffer read FSM 
-- Copyright (C) 2006 CESNET, Liberouter project
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
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
-- TODO: - 

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity tx_buf_fsm is
   port (
      -- Common interface
      RESET    : in std_logic;
      CLK      : in std_logic;

      -- Input
      RD       : in std_logic;
      EMPTY    : in std_logic;

      -- Output
      DV       : out std_logic;
      IDLE     : out std_logic
   );
end tx_buf_fsm;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of tx_buf_fsm is

type t_state is (WAIT_FOR_RD, READ_FIRST, READ_SECOND);
signal present_state, next_state: t_state; 

begin
-- -------------------------------------------------------
sync_logic : process(RESET, CLK)
begin
   if (RESET = '1') then
      present_state <= WAIT_FOR_RD;
   elsif (CLK'event AND CLK = '1') then
      present_state <= next_state;
   end if;
end process sync_logic;

-- -------------------------------------------------------
next_state_logic : process(present_state, RD, EMPTY)
begin
   case (present_state) is
   -- - - - - - - - - - - - - - - - - - - - -
   when WAIT_FOR_RD =>
      next_state <= WAIT_FOR_RD;
      if (RD = '1') then
         next_state <= READ_FIRST;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when READ_FIRST =>
      if (EMPTY = '0') then
         next_state <= WAIT_FOR_RD;
      else
         next_state <= READ_SECOND;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when READ_SECOND =>
      if (RD = '0') then
         next_state <= WAIT_FOR_RD;
      else
         next_state <= READ_FIRST;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when others =>
      null;
   -- - - - - - - - - - - - - - - - - - - - -
   end case;
end process;

-- -------------------------------------------------------
output_logic: process(present_state, EMPTY)
begin
   DV <= '0';
   IDLE <= '0';

   case (present_state) is
   -- - - - - - - - - - - - - - - - - - - - -
   when READ_FIRST =>
      DV <= not EMPTY;
   -- - - - - - - - - - - - - - - - - - - - -
   when READ_SECOND =>
      IDLE <= EMPTY;
      DV <= '1';
   -- - - - - - - - - - - - - - - - - - - - -
   when others =>
      null;
   -- - - - - - - - - - - - - - - - - - - - -
   end case;
end process;

end behavioral;

