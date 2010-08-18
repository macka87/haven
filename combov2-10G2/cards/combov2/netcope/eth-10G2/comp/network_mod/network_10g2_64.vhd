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
use work.network_mod_10g2_64_const.all;
use work.combov2_user_const.all;
use work.ibuf_general_pkg.all;
use work.lb_pkg.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of NETWORK_MOD_10G2_64 is

   -- ----------------- Constants declaration --------------------------------
   constant IBUF_DFIFO_SIZE   : integer := 8*IBUF_DFIFO_BYTES/DATA_WIDTH;
   constant IBUF_HFIFO_SIZE   : integer := 8*IBUF_HFIFO_BYTES/DATA_WIDTH;

   constant OBUF_DFIFO_SIZE   : integer := 8*OBUF_DFIFO_BYTES/DATA_WIDTH;
   constant OBUF_HFIFO_SIZE   : integer := 8*OBUF_HFIFO_BYTES/DATA_WIDTH;

   -- ------------------ Signals declaration ----------------------------------
   -- MI32 form MI Splitter to IBUF
   signal mi32_ibuf_dwr    : std_logic_vector(31 downto 0);
   signal mi32_ibuf_addr   : std_logic_vector(31 downto 0);
   signal mi32_ibuf_rd     : std_logic;
   signal mi32_ibuf_wr     : std_logic;
   signal mi32_ibuf_be     : std_logic_vector(3 downto 0);
   signal mi32_ibuf_drd    : std_logic_vector(31 downto 0);
   signal mi32_ibuf_ardy   : std_logic;
   signal mi32_ibuf_drdy   : std_logic;
   
   -- MI32 form MI Splitter to OBUF
   signal mi32_obuf_dwr    : std_logic_vector(31 downto 0);
   signal mi32_obuf_addr   : std_logic_vector(31 downto 0);
   signal mi32_obuf_rd     : std_logic;
   signal mi32_obuf_wr     : std_logic;
   signal mi32_obuf_be     : std_logic_vector(3 downto 0);
   signal mi32_obuf_drd    : std_logic_vector(31 downto 0);
   signal mi32_obuf_ardy   : std_logic;
   signal mi32_obuf_drdy   : std_logic;
   
   signal mi32_ibuf : t_mi32;
   signal mi32_obuf : t_mi32;
   
   signal ibuf0_stat          : t_ibuf_general_stat;
   signal ibuf1_stat          : t_ibuf_general_stat;
   signal ibuf0_link_up       : std_logic;
   signal ibuf1_link_up       : std_logic;
   signal ibuf0_link_up_f     : std_logic;
   signal ibuf1_link_up_f     : std_logic;
   signal ibuf0_incoming_pckt : std_logic;
   signal ibuf1_incoming_pckt : std_logic;

   signal obuf_outgoing_pckt  : std_logic_vector(1 downto 0);

begin

   -- MI_SPLITTER for IBUF and OBUF -------------------------------------------
   MI_SPLITTER_I: entity work.MI_SPLITTER
   generic map(
      ITEMS      => 2,
      ADDR_WIDTH => 12,
      DATA_WIDTH => 32,
      PIPE       => false
   )
   port map(
      -- Common interface
      CLK      => USER_CLK,
      RESET    => BUSRESET,

      -- Input MI interface
      IN_DWR   => MI32_DWR,
      IN_ADDR  => MI32_ADDR(12 downto 0),
      IN_BE    => MI32_BE,
      IN_RD    => MI32_RD,
      IN_WR    => MI32_WR,
      IN_ARDY  => MI32_ARDY,
      IN_DRD   => MI32_DRD,
      IN_DRDY  => MI32_DRDY,

      -- Output MI interfaces
      OUT_DWR(31 downto  0)  => mi32_obuf_dwr,
      OUT_DWR(63 downto 32)  => mi32_ibuf_dwr,
      OUT_ADDR(11 downto  0) => mi32_obuf_addr(11 downto 0),
      OUT_ADDR(23 downto 12) => mi32_ibuf_addr(11 downto 0),
      OUT_BE(3 downto 0)     => mi32_obuf_be,
      OUT_BE(7 downto 4)     => mi32_ibuf_be,
      OUT_RD(0)   => mi32_obuf_rd,
      OUT_RD(1)   => mi32_ibuf_rd,
      OUT_WR(0)   => mi32_obuf_wr,
      OUT_WR(1)   => mi32_ibuf_wr,
      OUT_ARDY(0) => mi32_obuf_ardy,
      OUT_ARDY(1) => mi32_ibuf_ardy,
      OUT_DRD(31 downto  0) => mi32_obuf_drd,
      OUT_DRD(63 downto 32) => mi32_ibuf_drd,
      OUT_DRDY(0) => mi32_obuf_drdy,
      OUT_DRDY(1) => mi32_ibuf_drdy
   );
   
   mi32_ibuf_addr(31 downto 12) <= (others => '0');
   mi32_obuf_addr(31 downto 12) <= (others => '0');
   
--    mi32_ibuf.dwr  <= mi32_ibuf_dwr;
--    mi32_ibuf.addr <= "00000000000000000000" & mi32_ibuf_addr;
--    mi32_ibuf.rd   <= mi32_ibuf_rd;
--    mi32_ibuf.wr   <= mi32_ibuf_wr;
--    mi32_ibuf.be   <= mi32_ibuf_be;
--    mi32_ibuf.rd   <= mi32_ibuf_rd;
--    mi32_ibuf_drd  <= mi32_ibuf.drd;
--    mi32_ibuf_ardy <= mi32_ibuf.ardy;
--    mi32_ibuf_drdy <= mi32_ibuf.drdy;
--    
--    mi32_obuf.dwr  <= mi32_obuf_dwr;
--    mi32_obuf.addr <= "00000000000000000000" & mi32_obuf_addr;
--    mi32_obuf.rd   <= mi32_obuf_rd;
--    mi32_obuf.wr   <= mi32_obuf_wr;
--    mi32_obuf.be   <= mi32_obuf_be;
--    mi32_obuf.rd   <= mi32_obuf_rd;
--    mi32_obuf_drd  <= mi32_obuf.drd;
--    mi32_obuf_ardy <= mi32_obuf.ardy;
--    mi32_obuf_drdy <= mi32_obuf.drdy;
   
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
      IBUF0_FRAME_RECEIVED => IBUF0_FRAME_RECEIVED,
      IBUF0_FRAME_DISCARDED=> IBUF0_FRAME_DISCARDED,
      IBUF0_BUFFER_OVF     => IBUF0_BUFFER_OVF,

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
      IBUF1_FRAME_RECEIVED => IBUF1_FRAME_RECEIVED,
      IBUF1_FRAME_DISCARDED=> IBUF1_FRAME_DISCARDED,
      IBUF1_BUFFER_OVF     => IBUF1_BUFFER_OVF,

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
      MI.DWR               => mi32_ibuf_dwr,
      MI.ADDR              => mi32_ibuf_addr,
      MI.RD                => mi32_ibuf_rd,
      MI.WR                => mi32_ibuf_wr,
      MI.BE                => mi32_ibuf_be,
      MI.DRD               => mi32_ibuf_drd,
      MI.ARDY              => mi32_ibuf_ardy,
      MI.DRDY              => mi32_ibuf_drdy,
      
      MI_CLK         => USER_CLK
   );

   IBUF0_PAYLOAD_LEN       <= ibuf0_stat.PAYLOAD_LEN;
   IBUF0_FRAME_ERROR       <= ibuf0_stat.FRAME_ERROR;
   IBUF0_CRC_CHECK_FAILED  <= ibuf0_stat.CRC_CHECK_FAILED;
   IBUF0_MAC_CHECK_FAILED  <= ibuf0_stat.MAC_CHECK_FAILED;
   IBUF0_LEN_BELOW_MIN     <= ibuf0_stat.LEN_BELOW_MIN;
   IBUF0_LEN_OVER_MTU      <= ibuf0_stat.LEN_OVER_MTU;

   glitch_filter_0 : entity work.glitch_filter
      generic map(
         FILTER_LENGTH     => 4,
         FILTER_SAMPLING   => 24,
         INIT              => '0'
      )
      port map(
         CLK         => XGMII_RXCLK(0),
         RESET       => FL_RESET,
         DIN         => ibuf0_link_up,
         DOUT        => ibuf0_link_up_f
      );

   glitch_filter_1 : entity work.glitch_filter
      generic map(
         FILTER_LENGTH     => 4,
         FILTER_SAMPLING   => 24,
         INIT              => '0'
      )
      port map(
         CLK         => XGMII_RXCLK(1),
         RESET       => FL_RESET,
         DIN         => ibuf1_link_up,
         DOUT        => ibuf1_link_up_f
      );

   LED_CTRL_IBUF0_I: entity work.led_ctrl
      generic map (
         CNTR_SIZE            => LED_CNTR_SIZE
      )
      port map (
         CLK                  => XGMII_RXCLK(0),
         RESET                => FL_RESET,
         LINE_UP              => ibuf0_link_up_f,
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
         LINE_UP              => ibuf1_link_up_f,
         PACKET               => ibuf1_incoming_pckt,
         LED                  => IBUF_LED(1)
      );

   -- Link presence signals (for interrupts)
   LINK0		   <= ibuf0_link_up_f;
   LINK1		   <= ibuf1_link_up_f;


   OBUF_I : entity work.obuf_xgmii_sdr_top2_mi32
      generic map(
         CTRL_CMD       => OBUF_CTRL_CMD,
         FL_WIDTH_RX    => DATA_WIDTH,
         DFIFO_SIZE     => OBUF_DFIFO_SIZE,
         HFIFO_SIZE     => OBUF_HFIFO_SIZE,
         HFIFO_MEMTYPE  => OBUF_HFIFO_MEMTYPE
      )
      port map(
         -- ---------------- Control signal -----------------
         FL_RESET      => FL_RESET,
         FL_CLK        => USER_CLK,
   
         -- 2 XGMII interfaces
         XGMII_RESET          => XGMII_RESET,
         XGMII_TXCLK          => XGMII_TXCLK,
         XGMII_TXD            => XGMII_TXD,
         XGMII_TXC            => XGMII_TXC,

         -- -------------- Buffer interface -----------------
         -- Interface 0
         OBUF0_RX_DATA        => OBUF0_RX_DATA,
         OBUF0_RX_REM         => OBUF0_RX_REM,
         OBUF0_RX_SRC_RDY_N   => OBUF0_RX_SRC_RDY_N,
         OBUF0_RX_SOF_N       => OBUF0_RX_SOF_N,
         OBUF0_RX_SOP_N       => OBUF0_RX_SOP_N,
         OBUF0_RX_EOF_N       => OBUF0_RX_EOF_N,
         OBUF0_RX_EOP_N       => OBUF0_RX_EOP_N,
         OBUF0_RX_DST_RDY_N   => OBUF0_RX_DST_RDY_N,
         -- Interface 1 
         OBUF1_RX_DATA        => OBUF1_RX_DATA,
         OBUF1_RX_REM         => OBUF1_RX_REM,
         OBUF1_RX_SRC_RDY_N   => OBUF1_RX_SRC_RDY_N,
         OBUF1_RX_SOF_N       => OBUF1_RX_SOF_N,
         OBUF1_RX_SOP_N       => OBUF1_RX_SOP_N,
         OBUF1_RX_EOF_N       => OBUF1_RX_EOF_N,
         OBUF1_RX_EOP_N       => OBUF1_RX_EOP_N,
         OBUF1_RX_DST_RDY_N   => OBUF1_RX_DST_RDY_N,

         -- Status interface
         OUTGOING_PCKT        => obuf_outgoing_pckt,

         -- ---------- MI_32 bus signals ----------------
         MI.DWR               => mi32_obuf_dwr,
         MI.ADDR              => mi32_obuf_addr,
         MI.RD                => mi32_obuf_rd,
         MI.WR                => mi32_obuf_wr,
         MI.BE                => mi32_obuf_be,
         MI.DRD               => mi32_obuf_drd,
         MI.ARDY              => mi32_obuf_ardy,
         MI.DRDY              => mi32_obuf_drdy,
         
         MI_CLK               => USER_CLK,
         MI_RESET             => BUSRESET
      );

   LED_CTRL_OBUF0_I: entity work.led_ctrl
      generic map (
         CNTR_SIZE            => LED_CNTR_SIZE
      )
      port map (
         CLK                  => XGMII_TXCLK(0),
         RESET                => FL_RESET,
         LINE_UP              => '1',
         PACKET               => obuf_outgoing_pckt(0),
         LED                  => OBUF_LED(0)
      );

   LED_CTRL_OBUF1_I: entity work.led_ctrl
      generic map (
         CNTR_SIZE            => LED_CNTR_SIZE
      )
      port map (
         CLK                  => XGMII_TXCLK(1),
         RESET                => FL_RESET,
         LINE_UP              => '1',
         PACKET               => obuf_outgoing_pckt(1),
         LED                  => OBUF_LED(1)
      );

   IBUF1_PAYLOAD_LEN       <= ibuf1_stat.PAYLOAD_LEN;
   IBUF1_FRAME_ERROR       <= ibuf1_stat.FRAME_ERROR;
   IBUF1_CRC_CHECK_FAILED  <= ibuf1_stat.CRC_CHECK_FAILED;
   IBUF1_MAC_CHECK_FAILED  <= ibuf1_stat.MAC_CHECK_FAILED;
   IBUF1_LEN_BELOW_MIN     <= ibuf1_stat.LEN_BELOW_MIN;
   IBUF1_LEN_OVER_MTU      <= ibuf1_stat.LEN_OVER_MTU;

end architecture full;
