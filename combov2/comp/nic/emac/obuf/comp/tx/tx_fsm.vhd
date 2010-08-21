-- tx_fsm.vhd: FSM for TX part of EMAC OBUF
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
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

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;


-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity obuf_emac_tx_fsm is

   port(
      -- Asynchronous reset
      RESET       : in std_logic;
      -- Clock signal
      CLK         : in std_logic;
      -- Clock enable signal
      CE          : in std_logic;

      -- Valid data is incoming to TX part
      RX_DVLD     : in std_logic;
      -- ACK signal from EMAC
      EMAC_ACK    : in std_logic;

      -- Next word should be sent from Buf part
      RX_NEXT     : out std_logic;
      -- Valid data is being transmitted
      TX_DVLD     : out std_logic
   );

end entity obuf_emac_tx_fsm;

-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
architecture full of obuf_emac_tx_fsm is

   -- Type definition
   type fsm_states is (st_idle, st_wait4ack, st_data);

   -- Signals declaration
   signal curr_state, next_state : fsm_states;

begin

   -- -------------------------------------------------------
   fsmp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         curr_state <= st_idle;
      elsif (CLK'event AND CLK = '1') then
         if (CE = '1') then
            curr_state <= next_state;
         end if;
      end if;
   end process;


   -- -------------------------------------------------------
   transition_logic: process(curr_state, RX_DVLD, EMAC_ACK)
   begin
      case (curr_state) is

         -- st_idle
         when st_idle =>
            if (RX_DVLD = '1') then
               next_state <= st_wait4ack;
               TX_DVLD <= '1';
               RX_NEXT <= '0';
            else
               next_state <= st_idle;
               TX_DVLD <= '0';
               RX_NEXT <= '1';
            end if;

         -- st_wait4ack
         when st_wait4ack =>
            TX_DVLD <= '1';
            if (EMAC_ACK = '1') then
               next_state <= st_data;
               RX_NEXT <= '1';
            else
               next_state <= st_wait4ack;
               RX_NEXT <= '0';
            end if;

         -- st_data
         when st_data =>
            if (RX_DVLD = '1') then
               next_state <= st_data;
               TX_DVLD <= '1';
               RX_NEXT <= '1';
            else
               next_state <= st_idle;
               TX_DVLD <= '0';
               RX_NEXT <= '0';
            end if;

      end case;
   end process transition_logic;

end architecture full;
