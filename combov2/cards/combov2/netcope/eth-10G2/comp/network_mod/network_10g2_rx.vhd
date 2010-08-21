-- network_10g2.vhd: Network Module for 2x10Gbps Combo2 interface card
-- Copyright (C) 2008 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;
use work.network_mod_10g2_rx_const.all;
use work.combov2_user_const.all;
use work.ibuf_general_pkg.all;
use work.lb_pkg.all;
use work.xgmii_pkg.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of NETWORK_MOD_10G2_RX is

   -- ----------------- Constants declaration --------------------------------
   constant IBUF_DFIFO_SIZE   : integer := 8*IBUF_DFIFO_BYTES/DATA_WIDTH;
   constant IBUF_HFIFO_SIZE   : integer := 8*IBUF_HFIFO_BYTES/DATA_WIDTH;

   -- ------------------ Signals declaration ----------------------------------
   signal mi32_ibuf : t_mi32;

   signal ibuf0_stat          : t_ibuf_general_stat;
   signal ibuf1_stat          : t_ibuf_general_stat;
   signal ibuf0_link_up       : std_logic;
   signal ibuf1_link_up       : std_logic;
   signal ibuf0_incoming_pckt : std_logic;
   signal ibuf1_incoming_pckt : std_logic;

begin
   
   mi32_ibuf.dwr  <= MI32_DWR; 
   mi32_ibuf.addr <= MI32_ADDR;
   mi32_ibuf.rd   <= MI32_RD;  
   mi32_ibuf.wr   <= MI32_WR;  
   mi32_ibuf.be   <= MI32_BE;  
   mi32_ibuf.rd   <= MI32_RD;  
   MI32_DRD       <= mi32_ibuf.drd;
   MI32_ARDY      <= mi32_ibuf.ardy;
   MI32_DRDY      <= mi32_ibuf.drdy;
   
   
   -- -------------------------------------------------------------------------
   --                               XGMII IBUF
   -- -------------------------------------------------------------------------
   IBUF_I : entity work.ibuf_xgmii_sdr_top2_mi32
   generic map(
      DFIFO_SIZE        => IBUF_DFIFO_SIZE,
      HFIFO_SIZE        => IBUF_HFIFO_SIZE,
      HFIFO_MEMTYPE     => IBUF_HFIFO_MEMTYPE,
      CTRL_HDR_EN       => PACODAG_HEADER_EN,
      CTRL_FTR_EN       => PACODAG_FOOTER_EN,
      CNT_ERROR_SIZE    => IBUF_CNT_ERROR_SIZE,
      MACS              => IBUF_MACS,
      INBANDFCS         => INBANDFCS,
      FL_WIDTH_TX       => DATA_WIDTH,
      FL_RELAY          => IBUF_FL_RELAY
   )
   port map(
      -- ---------------- Common signal -----------------
      RESET                => FL_RESET,
      FL_CLK               => USER_CLK,
      -- ------------------------------------------------
      -- -------------- IBUF interfaces -----------------
      -- -----------
      -- INTERFACE 0
      -- XGMII RX interface
      IBUF0_RXCLK          => XGMII_RXCLK(0),
      IBUF0_RXD            => XGMII_RXD(63 downto 0),
      IBUF0_RXC            => XGMII_RXC(7 downto 0),

      -- Sampling unit interface
      IBUF0_SAU_CLK        => IBUF0_SAU_CLK,
      IBUF0_SAU_RESET      => IBUF0_SAU_RESET,
      IBUF0_SAU_REQ        => IBUF0_SAU_REQ,
      IBUF0_SAU_ACCEPT     => IBUF0_SAU_ACCEPT,
      IBUF0_SAU_DV         => IBUF0_SAU_DV,
      
      -- PACODAG interface
      IBUF0_CTRL_CLK       => IBUF0_CTRL_CLK,
      IBUF0_CTRL_RESET     => IBUF0_CTRL_RESET,
      IBUF0_CTRL_DATA      => IBUF0_CTRL_DATA,
      IBUF0_CTRL_REM       => IBUF0_CTRL_REM,
      IBUF0_CTRL_SRC_RDY_N => IBUF0_CTRL_SRC_RDY_N,
      IBUF0_CTRL_SOP_N     => IBUF0_CTRL_SOP_N,
      IBUF0_CTRL_EOP_N     => IBUF0_CTRL_EOP_N,
      IBUF0_CTRL_DST_RDY_N => IBUF0_CTRL_DST_RDY_N,
      IBUF0_CTRL_RDY       => IBUF0_CTRL_RDY,

      -- IBUF status interface
      IBUF0_CTRL_SOP       => IBUF0_SOP,
      IBUF0_STAT           => ibuf0_stat,
      IBUF0_STAT_DV        => IBUF0_STAT_DV,

      -- State of the link signals
      IBUF0_LINK_UP        => ibuf0_link_up,
      IBUF0_INCOMING_PCKT  => ibuf0_incoming_pckt,

      -- FrameLink interface
      IBUF0_TX_DATA        => IBUF0_TX_DATA,
      IBUF0_TX_REM         => IBUF0_TX_REM,
      IBUF0_TX_SRC_RDY_N   => IBUF0_TX_SRC_RDY_N,
      IBUF0_TX_SOF_N       => IBUF0_TX_SOF_N,
      IBUF0_TX_SOP_N       => IBUF0_TX_SOP_N,
      IBUF0_TX_EOF_N       => IBUF0_TX_EOF_N,
      IBUF0_TX_EOP_N       => IBUF0_TX_EOP_N,
      IBUF0_TX_DST_RDY_N   => IBUF0_TX_DST_RDY_N,
      
      -- -----------
      -- INTERFACE 1
      -- XGMII RX interface
      IBUF1_RXCLK          => XGMII_RXCLK(1),
      IBUF1_RXD            => XGMII_RXD(127 downto 64),
      IBUF1_RXC            => XGMII_RXC( 15 downto  8),

      -- Sampling unit interface
      IBUF1_SAU_CLK        => IBUF1_SAU_CLK,
      IBUF1_SAU_RESET      => IBUF1_SAU_RESET,
      IBUF1_SAU_REQ        => IBUF1_SAU_REQ,
      IBUF1_SAU_ACCEPT     => IBUF1_SAU_ACCEPT,
      IBUF1_SAU_DV         => IBUF1_SAU_DV,

      -- PACODAG interface
      IBUF1_CTRL_CLK       => IBUF1_CTRL_CLK,
      IBUF1_CTRL_RESET     => IBUF1_CTRL_RESET,
      IBUF1_CTRL_DATA      => IBUF1_CTRL_DATA,
      IBUF1_CTRL_REM       => IBUF1_CTRL_REM,
      IBUF1_CTRL_SRC_RDY_N => IBUF1_CTRL_SRC_RDY_N,
      IBUF1_CTRL_SOP_N     => IBUF1_CTRL_SOP_N,
      IBUF1_CTRL_EOP_N     => IBUF1_CTRL_EOP_N,
      IBUF1_CTRL_DST_RDY_N => IBUF1_CTRL_DST_RDY_N,
      IBUF1_CTRL_RDY       => IBUF1_CTRL_RDY,

      -- IBUF status interface
      IBUF1_CTRL_SOP       => IBUF1_SOP,
      IBUF1_STAT           => ibuf1_stat,
      IBUF1_STAT_DV        => IBUF1_STAT_DV,

      -- State of the link signals
      IBUF1_LINK_UP        => ibuf1_link_up,
      IBUF1_INCOMING_PCKT  => ibuf1_incoming_pckt,

      -- FrameLink interface
      IBUF1_TX_DATA        => IBUF1_TX_DATA,
      IBUF1_TX_REM         => IBUF1_TX_REM,
      IBUF1_TX_SRC_RDY_N   => IBUF1_TX_SRC_RDY_N,
      IBUF1_TX_SOF_N       => IBUF1_TX_SOF_N,
      IBUF1_TX_SOP_N       => IBUF1_TX_SOP_N,
      IBUF1_TX_EOF_N       => IBUF1_TX_EOF_N,
      IBUF1_TX_EOP_N       => IBUF1_TX_EOP_N,
      IBUF1_TX_DST_RDY_N   => IBUF1_TX_DST_RDY_N,

      -- ------------------------------------------------
      -- ------------ MI_32 bus signals -----------------
      MI             => mi32_ibuf,
      MI_CLK         => USER_CLK
   );

   IBUF0_PAYLOAD_LEN       <= ibuf0_stat.PAYLOAD_LEN;
   IBUF0_FRAME_ERROR       <= ibuf0_stat.FRAME_ERROR;
   IBUF0_CRC_CHECK_FAILED  <= ibuf0_stat.CRC_CHECK_FAILED;
   IBUF0_MAC_CHECK_FAILED  <= ibuf0_stat.MAC_CHECK_FAILED;
   IBUF0_LEN_BELOW_MIN     <= ibuf0_stat.LEN_BELOW_MIN;
   IBUF0_LEN_OVER_MTU      <= ibuf0_stat.LEN_OVER_MTU;

   IBUF1_PAYLOAD_LEN       <= ibuf1_stat.PAYLOAD_LEN;
   IBUF1_FRAME_ERROR       <= ibuf1_stat.FRAME_ERROR;
   IBUF1_CRC_CHECK_FAILED  <= ibuf1_stat.CRC_CHECK_FAILED;
   IBUF1_MAC_CHECK_FAILED  <= ibuf1_stat.MAC_CHECK_FAILED;
   IBUF1_LEN_BELOW_MIN     <= ibuf1_stat.LEN_BELOW_MIN;
   IBUF1_LEN_OVER_MTU      <= ibuf1_stat.LEN_OVER_MTU;

   LED_CTRL_IBUF0_I: entity work.led_ctrl
      generic map (
         CNTR_SIZE            => LED_CNTR_SIZE
      )
      port map (
         CLK                  => XGMII_RXCLK(0),
         RESET                => FL_RESET,
         LINE_UP              => ibuf0_link_up,
         PACKET               => ibuf0_incoming_pckt,
         LED                  => IBUF_LED(0)
      );
   LED_CTRL_IBUF1_I: entity work.led_ctrl
      generic map (
         CNTR_SIZE            => LED_CNTR_SIZE
      )
      port map (
         CLK                  => XGMII_RXCLK(1),
         RESET                => FL_RESET,
         LINE_UP              => ibuf1_link_up,
         PACKET               => ibuf1_incoming_pckt,
         LED                  => IBUF_LED(1)
      );

   -- Link presence signals
   LINK0 <= ibuf0_link_up;
   LINK1 <= ibuf1_link_up;

   -- Turn OBUF LEDS on (always when the design is loaded)
   OBUF_LED <= (others => '0');

   -- set idle command on TX XGMII channels
      -- channel 0
   XGMII_TXD(63 downto 0)   <= C_XGMII_IDLE_WORD64;
   XGMII_TXC(7 downto 0)    <= (others => '1');
      -- channel 1
   XGMII_TXD(127 downto 64) <= C_XGMII_IDLE_WORD64;
   XGMII_TXC(15 downto 8)   <= (others => '1');

end architecture full;
