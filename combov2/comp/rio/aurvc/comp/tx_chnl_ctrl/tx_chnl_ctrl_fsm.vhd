
-- tx_chnl_ctrl_fsm.vhd: TX Channel Controller FSM 
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

entity tx_chnl_ctrl_fsm is
   port (
      -- Common Input
      CLK      : in std_logic;
      RESET    : in std_logic;

      -- Input
      CHANNEL_VALID                 : in std_logic;
      FIFO_DV                       : in std_logic;
      FIFO_EOP                      : in std_logic;
      FIFO_EMPTY                    : in std_logic;
      AUR_TX_DST_RDY_N              : in std_logic;
      CHANNEL_BYTE_QUOTA_MET        : in std_logic;

      -- Output
      CHANNEL_DATA_ID_MX            : out std_logic;
      AUR_TX_SRC_RDY_N              : out std_logic;
      AUR_TX_SOF_N                  : out std_logic;
      AUR_TX_EOF_N                  : out std_logic;
      FIFO_READ                     : out std_logic;
      REG_CHNL_MASK_RST_ENABLE      : out std_logic
   );
end tx_chnl_ctrl_fsm;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of tx_chnl_ctrl_fsm is

type t_state is (WAIT_FOR_CHNL, SEND_IFC_ID, SEND_PACKET);
signal present_state, next_state: t_state;  

begin
-- -------------------------------------------------------
sync_logic : process(RESET, CLK)
begin
   if (RESET = '1') then
      present_state <= WAIT_FOR_CHNL;
   elsif (CLK'event AND CLK = '1') then
      present_state <= next_state;
   end if;
end process sync_logic;

-- -------------------------------------------------------
next_state_logic : process(present_state, CHANNEL_VALID, FIFO_EOP, FIFO_EMPTY, AUR_TX_DST_RDY_N, CHANNEL_BYTE_QUOTA_MET)
begin
   case (present_state) is
   -- - - - - - - - - - - - - - - - - - - - -
   when WAIT_FOR_CHNL =>
      next_state <= WAIT_FOR_CHNL;
      if (CHANNEL_VALID = '1') then
         next_state <= SEND_IFC_ID;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when SEND_IFC_ID =>
      next_state <= SEND_IFC_ID;
      if (AUR_TX_DST_RDY_N = '0') then
         next_state <= SEND_PACKET;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when SEND_PACKET =>
      next_state <= SEND_PACKET;
      if (AUR_TX_DST_RDY_N = '0' and FIFO_EOP = '1') then
         if (FIFO_EMPTY = '1' or CHANNEL_BYTE_QUOTA_MET = '1' or CHANNEL_VALID = '0') then
            next_state <= WAIT_FOR_CHNL;        -- arbitrate next channel
         else
            next_state <= SEND_IFC_ID;          -- send next packet via the same channel
         end if;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when others =>
      next_state <= WAIT_FOR_CHNL;
   -- - - - - - - - - - - - - - - - - - - - -
   end case;
end process;
         
-- -------------------------------------------------------
output_logic: process(present_state, CHANNEL_VALID, FIFO_DV, FIFO_EOP, FIFO_EMPTY, AUR_TX_DST_RDY_N, CHANNEL_BYTE_QUOTA_MET)
begin
   CHANNEL_DATA_ID_MX         <= '0';
   AUR_TX_SRC_RDY_N           <= '1';
   AUR_TX_SOF_N               <= '1';
   AUR_TX_EOF_N               <= '1';
   FIFO_READ                  <= '0';
   REG_CHNL_MASK_RST_ENABLE   <= '0';

   case (present_state) is
   -- - - - - - - - - - - - - - - - - - - - -
   when SEND_IFC_ID =>
      CHANNEL_DATA_ID_MX   <= '1';
      AUR_TX_SRC_RDY_N     <= '0';
      AUR_TX_SOF_N         <= '0';
--      FIFO_READ            <= not AUR_TX_DST_RDY_N;
   -- - - - - - - - - - - - - - - - - - - - -
   when SEND_PACKET =>
      AUR_TX_SRC_RDY_N     <= not FIFO_DV;
      AUR_TX_EOF_N         <= not FIFO_EOP;
--      FIFO_READ            <= (not FIFO_EOP) and (not AUR_TX_DST_RDY_N);
      FIFO_READ            <= not AUR_TX_DST_RDY_N;
      REG_CHNL_MASK_RST_ENABLE   <= FIFO_EOP and (FIFO_EMPTY or CHANNEL_BYTE_QUOTA_MET);
   -- - - - - - - - - - - - - - - - - - - - -
   when others =>
      null;
   -- - - - - - - - - - - - - - - - - - - - -
   end case;
end process;
      
end behavioral;

