
-- recv_fsm.vhd: Reciever FSM 
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

entity recv_fsm is
   port (
      RESET       : in std_logic;
      CLK         : in std_logic;
      
      -- Input
      SOC_OCC     : in std_logic;
      TERM_OCC    : in std_logic;
      EMPTY       : in std_logic;
      CRC_VALID   : in std_logic;
      FULL        : in std_logic;

      -- Output
      STATUS_DV   : out std_logic;
      DO_DV       : out std_logic;
      FIFO_RD     : out std_logic;
      CRC_WE      : out std_logic
   );
end recv_fsm;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of recv_fsm is

type t_state is (WAIT_FOR_SOC, WAIT_FOR_TERM, WAIT_FOR_CRC, CONFIRM_STATUS);
signal present_state, next_state: t_state; 

begin
-- -------------------------------------------------------
sync_logic : process(RESET, CLK)
begin
   if (RESET = '1') then
      present_state <= WAIT_FOR_SOC;
   elsif (CLK'event AND CLK = '1') then
      present_state <= next_state;
   end if;
end process sync_logic;

-- -------------------------------------------------------
next_state_logic : process(present_state, SOC_OCC, TERM_OCC, CRC_VALID, EMPTY, FULL)
begin
   case (present_state) is
   -- - - - - - - - - - - - - - - - - - - - -
   when WAIT_FOR_SOC =>
      next_state <= WAIT_FOR_SOC;
      if (SOC_OCC = '1' and EMPTY = '0' and FULL = '0') then
         next_state <= WAIT_FOR_TERM;
      end if;
   -- - - - - - - - - - - - - - - - - - - - - 
   when WAIT_FOR_TERM =>
      next_state <= WAIT_FOR_TERM;
      if (TERM_OCC = '1' and EMPTY = '0' and FULL = '0') then
         next_state <= WAIT_FOR_CRC;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when WAIT_FOR_CRC =>
      next_state <= WAIT_FOR_CRC;
      if (CRC_VALID = '1' and EMPTY = '0' and FULL = '0') then
         next_state <= CONFIRM_STATUS;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when CONFIRM_STATUS =>
      next_state <= CONFIRM_STATUS;
      if (EMPTY = '0') then
         next_state <= WAIT_FOR_SOC;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when others =>
      next_state <= WAIT_FOR_SOC;
   -- - - - - - - - - - - - - - - - - - - - -
   end case;
end process;

output_logic: process(present_state, EMPTY, TERM_OCC, CRC_VALID)
begin
   DO_DV    <= '0';
   STATUS_DV<= '0';
   FIFO_RD  <= '1';
   CRC_WE   <= '0';

   case (present_state) is
   -- - - - - - - - - - - - - - - - - - - - -
   when WAIT_FOR_SOC =>
      DO_DV <= not EMPTY;
   -- - - - - - - - - - - - - - - - - - - - -
   when WAIT_FOR_TERM =>
      DO_DV <= not EMPTY;
   -- - - - - - - - - - - - - - - - - - - - -
   when WAIT_FOR_CRC =>
      FIFO_RD <= CRC_VALID;
      CRC_WE  <= '1';
   -- - - - - - - - - - - - - - - - - - - - -
   when CONFIRM_STATUS =>
      STATUS_DV <= '1';
   -- - - - - - - - - - - - - - - - - - - - -
   when others =>
      null;
   -- - - - - - - - - - - - - - - - - - - - -
   end case;
end process;

end behavioral;

