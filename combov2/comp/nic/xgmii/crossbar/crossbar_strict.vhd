-- crossbar_strict.vhd: XGMII to XGMII crossbar with XGMII checking
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
use work.xgmii_pkg.ALL; -- C_XGMII_IDLE_WORD64

---
-- Entity
---
entity xgmii_crossbar_strict is
   generic (
      XGMII_COUNT : integer := 6
   );
   port (
      CLK         : in std_logic;
      RESET       : in std_logic;

      --+ XGMII RX
      XGMII_RXC   : in std_logic_vector
                        (XGMII_COUNT * 8 - 1 downto 0);
      XGMII_RXD   : in std_logic_vector
                        (XGMII_COUNT * 64 - 1 downto 0);
      --+ Packet info RX
      RX_SOP      : in std_logic_vector(XGMII_COUNT - 1 downto 0);
      RX_EOP      : in std_logic_vector(XGMII_COUNT - 1 downto 0);

      --+ XGMII TX
      XGMII_TXC   : out std_logic_vector
                        (XGMII_COUNT * 8 - 1 downto 0);
      XGMII_TXD   : out std_logic_vector
                        (XGMII_COUNT * 64 - 1 downto 0);
      --+ Packet info TX
      TX_SOP      : out std_logic_vector(XGMII_COUNT - 1 downto 0);
      TX_EOP      : out std_logic_vector(XGMII_COUNT - 1 downto 0);

      --+ Configuration
      --* <pre>| src(0) | ... | src(XGMII_COUNT - 1) |</pre>
      --* mapping:
      --*   TX(i) <= RX(src(i))
      MAPPING     : in std_logic_vector
                        (XGMII_COUNT * log2(XGMII_COUNT) - 1 downto 0);
      MAPPING_WE  : in std_logic
   );
end entity;

---
-- Architecture
---
architecture behav of xgmii_crossbar_strict is

   constant MAP_WIDTH   : integer := log2(XGMII_COUNT);
   constant XGMII_IDLE_CTRL : std_logic_vector(7 downto 0) 
                                          := (others => '1');

   signal rx_inside_packet : std_logic_vector(XGMII_COUNT - 1 downto 0);
   signal tx_inside_packet : std_logic_vector(XGMII_COUNT - 1 downto 0);
   signal crossbar_map  : std_logic_vector
                        (XGMII_COUNT * log2(XGMII_COUNT) - 1 downto 0);
   signal sel_idle      : std_logic_vector(XGMII_COUNT - 1 downto 0);

   signal mux_xgmii_txc  : std_logic_vector(XGMII_COUNT *  8 - 1 downto 0);
   signal mux_xgmii_txd  : std_logic_vector(XGMII_COUNT * 64 - 1 downto 0);

   signal mux_tx_sop     : std_logic_vector(XGMII_COUNT - 1 downto 0);
   signal mux_tx_eop     : std_logic_vector(XGMII_COUNT - 1 downto 0);

begin

   ---
   -- Strict mechanism using packet+remap_fsm
   ---
   foreach_port_gen_fsm:
   for i in 0 to XGMII_COUNT - 1 generate

      -- monitoring RX port
      rx_fsm_i : entity work.packet_fsm
      port map (
         CLK   => CLK,
         RESET => RESET,

         SOP   => RX_SOP(i),
         EOP   => RX_EOP(i),
         INSIDE_PACKET  => rx_inside_packet(i)
      );
      
      -- monitoring TX port
      tx_fsm_i : entity work.packet_fsm
      port map (
         CLK   => CLK,
         RESET => RESET,

         SOP         => mux_tx_sop(i),
         EOP         => mux_tx_eop(i),
         INSIDE_PACKET  => tx_inside_packet(i)
      );
      
      -- port remapping logic
      remap_fsm_i : entity work.remap_fsm
      generic map (
         XGMII_PORTS => XGMII_COUNT
      )
      port map (
         CLK   => CLK,
         RESET => RESET,

         RX_INSIDE_PACKET  => rx_inside_packet,
         TX_INSIDE_PACKET  => tx_inside_packet(i),
--         TX_INSIDE_PACKET  => rx_inside_packet(i),

         MAPPING_REQ => MAPPING_WE,
         MAPPING_IN  => MAPPING((i + 1) * MAP_WIDTH - 1 downto i * MAP_WIDTH),
         MAPPING_ACK => open,

         MAPPING_OUT => crossbar_map((i + 1) * MAP_WIDTH - 1 downto i * MAP_WIDTH),
         SEL_IDLE    => sel_idle(i)
      );

   end generate;

   ---
   -- Idle/Pass multiplexors
   ---
   foreach_port_gen_mux:
   for i in 0 to XGMII_COUNT - 1 generate

      ---
      -- Data output multiplexor
      ---
      with sel_idle(i) select
      XGMII_TXD((i + 1) * 64 - 1 downto i * 64)
         <= mux_xgmii_txd((i + 1) * 64 - 1 downto i * 64)   when '0',
            C_XGMII_IDLE_WORD64                             when others;
                    
      ---
      -- Ctrl output multiplexor
      ---
      with sel_idle(i) select
      XGMII_TXC((i + 1) *  8 - 1 downto i *  8)
         <= mux_xgmii_txc((i + 1) *  8 - 1 downto i *  8)   when '0',
            XGMII_IDLE_CTRL                                 when others;

      TX_SOP(i)   <= mux_tx_sop(i)  when sel_idle(i) = '0' else '0';
      TX_EOP(i)   <= mux_tx_eop(i)  when sel_idle(i) = '0' else '0';

   end generate;

   ---
   -- Generic crossbar instantiation
   ---
   CROSSBAR_GEN_U : entity work.XGMII_CROSSBAR
   generic map (
      XGMII_COUNT => XGMII_COUNT
   )
   port map (
      --+ ports
      XGMII_RXC   => XGMII_RXC,
      XGMII_RXD   => XGMII_RXD,
      XGMII_TXC   => mux_xgmii_txc,
      XGMII_TXD   => mux_xgmii_txd,

      RX_SOP      => RX_SOP,
      RX_EOP      => RX_EOP,
      TX_SOP      => mux_tx_sop,
      TX_EOP      => mux_tx_eop,

      --+ configuration of the crossbar
      MAPPING     => crossbar_map
   );

end architecture;
