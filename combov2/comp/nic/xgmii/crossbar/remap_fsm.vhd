-- remap_fsm.vhd: Drives the safe mapping change
-- Copyright (C) 2010 CESNET
-- Author(s):  Jan Viktorin <xvikto03@liberouter.org>
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

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

use work.math_pack.ALL;

---
-- Entity
---
entity remap_fsm is
   generic (
      XGMII_PORTS    : integer;
      INIT_MAPPING   : integer := 0
   );
   port (
      CLK   : in std_logic;
      RESET : in std_logic;

      --+ get know (from packet_fsm) if the RX is inside packet or not
      RX_INSIDE_PACKET  : in std_logic_vector(XGMII_PORTS - 1 downto 0);
      --+ get know (from packet_fsm) if the TX is inside packet or not
      TX_INSIDE_PACKET  : in std_logic;

      --+ request to change mapping
      MAPPING_REQ    : in std_logic;
      --+ mapping accepted 
      MAPPING_ACK    : out std_logic;
      --+ new mapping for current port
      MAPPING_IN     : in std_logic_vector(log2(XGMII_PORTS) - 1 downto 0);

      --+ result mapping of the crossbar port
      MAPPING_OUT    : out std_logic_vector(log2(XGMII_PORTS) - 1 downto 0);
      --+ pass XGMII idle to the TX or pass real data
      SEL_IDLE       : out std_logic
   );
end entity;

---
-- Architecture
---
architecture behav of remap_fsm is

   type state_t is (st_wait, st_wait_rxgap, st_wait_txgap);

   signal state      : state_t;
   signal next_state : state_t;

   signal reg_map       : std_logic_vector(log2(XGMII_PORTS) - 1 downto 0);
   signal reg_map_ce    : std_logic;
   signal reg_newmap    : std_logic_vector(log2(XGMII_PORTS) - 1 downto 0);
   signal reg_newmap_ce : std_logic;

   signal mapping_request : std_logic;

begin

   MAPPING_OUT       <= reg_map;
   mapping_request   <= MAPPING_REQ when reg_map /= MAPPING_IN
                        else '0';

   new_register_mapping : process(CLK, RESET, reg_newmap_ce, MAPPING_IN)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            reg_newmap  <= conv_std_logic_vector(INIT_MAPPING,
                                                   log2(XGMII_PORTS));
         
         elsif reg_newmap_ce = '1' then
            reg_newmap  <= MAPPING_IN;

         end if;
      end if;
   end process;

   register_mapping : process(CLK, RESET, reg_map_ce, reg_newmap)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            reg_map  <= conv_std_logic_vector(INIT_MAPPING,
                                                log2(XGMII_PORTS));
         
         elsif reg_map_ce = '1' then
            reg_map  <= reg_newmap;

         end if;
      end if;
   end process;

   fsm_state: process(CLK, RESET, next_state)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            state <= st_wait;
         else
            state <= next_state;
         end if;
      end if;
   end process;

   fsm_next: process(CLK, state, RX_INSIDE_PACKET, TX_INSIDE_PACKET)
      variable rx_port : integer;
   begin
      next_state  <= state;
      rx_port  := conv_integer(reg_map);

      case state is
         when st_wait =>
            if mapping_request = '1' then
               next_state <= st_wait_rxgap;
            end if;

         when st_wait_rxgap =>
            if rx_port < XGMII_PORTS and RX_INSIDE_PACKET(rx_port) = '0' then
               next_state <= st_wait_txgap;
            end if;

         when st_wait_txgap =>
            if TX_INSIDE_PACKET = '0' then
               next_state <= st_wait;
            end if;

      end case;
   end process;

   fsm_output: process(CLK, state, RX_INSIDE_PACKET, TX_INSIDE_PACKET,
                        mapping_request, MAPPING_REQ, reg_map, MAPPING_IN)
      variable rx_port : integer;
   begin
      reg_newmap_ce  <= '0';
      reg_map_ce     <= '0';
      MAPPING_ACK    <= '0';
      rx_port  := conv_integer(reg_map);

      case state is
         when st_wait =>
            SEL_IDLE       <= '0';
            -- handle new mapping request (trasiting to st_wait_rxgap)
            reg_newmap_ce  <= mapping_request;

            -- when requesting to write the same mapping, only ACK
            if reg_map = MAPPING_IN then
               MAPPING_ACK <= MAPPING_REQ;
            end if;

         when st_wait_rxgap =>
            SEL_IDLE   <= '0';
            -- packet gap reached, use new mapping (transiting to st_wait_txgap)
            if rx_port < XGMII_PORTS then
               reg_map_ce <= not RX_INSIDE_PACKET(rx_port);
            end if;

         when st_wait_txgap =>
            -- send idle when inside packet
            SEL_IDLE    <= TX_INSIDE_PACKET;
            -- send ack when transiting to st_wait
            MAPPING_ACK <= not TX_INSIDE_PACKET;

      end case;
   end process;

end architecture;
