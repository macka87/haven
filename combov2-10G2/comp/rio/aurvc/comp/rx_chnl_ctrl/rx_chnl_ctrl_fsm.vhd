
-- rx_chnl_ctrl_fsm.vhd: RX Channel Controller FSM 
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

entity rx_chnl_ctrl_fsm is
   port (
      -- Common Input
      CLK      : in std_logic;
      RESET    : in std_logic;

      -- Input
      AUR_RX_SRC_RDY_N              : in std_logic;
      AUR_RX_SOF_N                  : in std_logic;
      AUR_RX_EOF_N                  : in std_logic;

      -- Output
      FIFO_WRITE                    : out std_logic;
      REG_IFC_ID_WE                 : out std_logic 
   );
end rx_chnl_ctrl_fsm;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of rx_chnl_ctrl_fsm is

type t_state is (WAIT_FOR_PACKET, RECEIVE_PACKET);
signal present_state, next_state: t_state;  

begin
-- -------------------------------------------------------
sync_logic : process(RESET, CLK)
begin
   if (RESET = '1') then
      present_state <= WAIT_FOR_PACKET;
   elsif (CLK'event AND CLK = '1') then
      present_state <= next_state;
   end if;
end process sync_logic;

-- -------------------------------------------------------
next_state_logic : process(present_state, AUR_RX_SRC_RDY_N, AUR_RX_SOF_N, AUR_RX_EOF_N)
begin
   case (present_state) is
   -- - - - - - - - - - - - - - - - - - - - -
   when WAIT_FOR_PACKET => 
      next_state <= WAIT_FOR_PACKET;
      if (AUR_RX_SRC_RDY_N = '0' and AUR_RX_SOF_N = '0') then
         next_state <= RECEIVE_PACKET;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when RECEIVE_PACKET => 
      next_state <= RECEIVE_PACKET;
      if (AUR_RX_SRC_RDY_N = '0' and AUR_RX_EOF_N = '0') then
         next_state <= WAIT_FOR_PACKET;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when others =>
      next_state <= WAIT_FOR_PACKET;
   -- - - - - - - - - - - - - - - - - - - - -
   end case;
end process;

-- -------------------------------------------------------
output_logic: process(present_state, AUR_RX_SRC_RDY_N, AUR_RX_SOF_N)
begin
   FIFO_WRITE                 <= '0';
   REG_IFC_ID_WE              <= '0';

   case (present_state) is
   -- - - - - - - - - - - - - - - - - - - - -
   when WAIT_FOR_PACKET => 
      REG_IFC_ID_WE <= (not AUR_RX_SRC_RDY_N) and (not AUR_RX_SOF_N); 
   -- - - - - - - - - - - - - - - - - - - - -
   when RECEIVE_PACKET => 
      FIFO_WRITE <= not AUR_RX_SRC_RDY_N;
   -- - - - - - - - - - - - - - - - - - - - -
   when others =>
      null;
   -- - - - - - - - - - - - - - - - - - - - -
   end case;
end process;
         
end behavioral;

