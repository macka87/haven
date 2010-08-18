-- xgmii_strict_mux.vhd : Generic multiplexor for XGMII
-- Copyright (C) 2010 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
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

-- --------------------------------------------------------------------
--                       Architecture declaration
-- --------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;

-- Math package - log2 function
use work.math_pack.all;
use work.xgmii_pkg.all; -- C_XGMII_IDLE_WORD64

architecture arch of xgmii_strict_mux is

   constant XGMII_IDLE_CTRL : std_logic_vector(7 downto 0) 
                                          := (others => '1');

   signal mux_tx_sop       : std_logic;
   signal mux_tx_eop       : std_logic;
   signal tx_inside_packet : std_logic;
   signal mux_sel          : std_logic_vector(log2(XGMII_COUNT) - 1 downto 0);
   signal mux_idle         : std_logic;

   signal mux_xgmii_txd    : std_logic_vector(63 downto 0);
   signal mux_xgmii_txc    : std_logic_vector( 7 downto 0);

begin

   -- XGMII multiplexor
   mux : entity work.xgmii_mux
   generic map (
      XGMII_COUNT => XGMII_COUNT
   )
   port map (
      XGMII_RXD   => XGMII_RXD,
      XGMII_RXC   => XGMII_RXC,
      RX_SOP      => RX_SOP,
      RX_EOP      => RX_EOP,

      XGMII_TXD   => mux_xgmii_txd,
      XGMII_TXC   => mux_xgmii_txc,
      TX_SOP      => mux_tx_sop,
      TX_EOP      => mux_tx_eop,

      SEL         => mux_sel
   );
  
   -- output mux
   XGMII_TXD   <= mux_xgmii_txd  
                  when mux_idle = '0' 
                  else C_XGMII_IDLE_WORD64;
   XGMII_TXC   <= mux_xgmii_txc  
                  when mux_idle = '0' 
                  else XGMII_IDLE_CTRL;

   TX_SOP   <= mux_tx_sop  when mux_idle = '0' else '0';
   TX_EOP   <= mux_tx_eop  when mux_idle = '0' else '0';


   -- monitoring TX port
   tx_fsm : entity work.packet_fsm
   port map (
      CLK   => CLK,
      RESET => RESET,

      SOP         => mux_tx_sop,
      EOP         => mux_tx_eop,
      INSIDE_PACKET  => tx_inside_packet
   );

   -- remap logic of the multiplexor
   remap_fsm : entity work.remap_fsm
   generic map (
      XGMII_PORTS    => XGMII_COUNT,
      INIT_MAPPING   => INIT_SEL
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,

      RX_INSIDE_PACKET  => RX_INSIDE_PACKET,
      TX_INSIDE_PACKET  => tx_inside_packet,

      MAPPING_REQ       => SEL_WE,
      MAPPING_ACK       => open,
      MAPPING_IN        => SEL,

      MAPPING_OUT       => mux_sel,
      SEL_IDLE          => mux_idle
   );

   SEL_OUT  <= mux_sel;
 
end architecture;

