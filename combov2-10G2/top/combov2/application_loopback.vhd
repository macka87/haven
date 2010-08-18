-- application_loopback.vhd : NetCOPE application with FrameLink loopback
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz>
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

-- ----------------------------------------------------------------------------
--                             Entity declaration
-- ----------------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all; 
use work.combov2_core_const.all;
use work.combov2_user_const.all;
use work.math_pack.all;
use work.ibuf_general_pkg.all;
use work.fl_pkg.all;
use work.addr_space.all;
use work.network_mod_10g2_const.all;

architecture full of APPLICATION is

   component tsu_async is
   -- PORTS
   port (
      RESET          : in std_logic;

      -- Input interface
      IN_CLK         : in std_logic;

      IN_TS          : in std_logic_vector(63 downto 0);
      IN_TS_DV       : in std_logic;

      -- Output interface
      OUT_CLK        : in std_logic;

      OUT_TS         : out std_logic_vector(63 downto 0);
      OUT_TS_DV      : out std_logic
   );
   end component tsu_async;

   component FL_WATCH_2 is
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      SOF_N          : in std_logic_vector(1 downto 0);
      EOF_N          : in std_logic_vector(1 downto 0);
      SOP_N          : in std_logic_vector(1 downto 0);
      EOP_N          : in std_logic_vector(1 downto 0);
      DST_RDY_N      : in std_logic_vector(1 downto 0);
      SRC_RDY_N      : in std_logic_vector(1 downto 0);

      FRAME_ERR      : out std_logic_vector(1 downto 0);

      MI_DWR	      : in std_logic_vector(31 downto 0);
      MI_ADDR        : in std_logic_vector(31 downto 0);
      MI_RD	         : in std_logic;
      MI_WR	         : in std_logic;
      MI_BE	         : in std_logic_vector(3 downto 0);
      MI_DRD         : out std_logic_vector(31 downto 0);
      MI_ARDY        : out std_logic;
      MI_DRDY        : out std_logic
   );
   end component;
-- ----------------------------------------------------------------------------
--                            Signal declaration
-- ----------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   --                            MI32 signals
   -- -------------------------------------------------------------------------
   -- MI32 to MI_SPLITTER to FL_WATCH instance
   signal mi32_watch_dwr         : std_logic_vector(31 downto 0);
   signal mi32_watch_addr        : std_logic_vector(31 downto 0);
   signal mi32_watch_rd          : std_logic;
   signal mi32_watch_wr          : std_logic;
   signal mi32_watch_be          : std_logic_vector(3 downto 0);
   signal mi32_watch_drd         : std_logic_vector(31 downto 0);
   signal mi32_watch_ardy        : std_logic;
   signal mi32_watch_drdy        : std_logic;

   -- MI32 to FL_WATCH in TX direction (application -> obuf)
   signal mi32_tx_watch_dwr      : std_logic_vector(31 downto 0);
   signal mi32_tx_watch_addr     : std_logic_vector(31 downto 0);
   signal mi32_tx_watch_rd       : std_logic;
   signal mi32_tx_watch_wr       : std_logic;
   signal mi32_tx_watch_be       : std_logic_vector(3 downto 0);
   signal mi32_tx_watch_drd      : std_logic_vector(31 downto 0);
   signal mi32_tx_watch_ardy     : std_logic;
   signal mi32_tx_watch_drdy     : std_logic;

   -- MI32 to FL_WATCH in RX direction (application -> ibuf)
   signal mi32_rx_watch_dwr      : std_logic_vector(31 downto 0);
   signal mi32_rx_watch_addr     : std_logic_vector(31 downto 0);
   signal mi32_rx_watch_rd       : std_logic;
   signal mi32_rx_watch_wr       : std_logic;
   signal mi32_rx_watch_be       : std_logic_vector(3 downto 0);
   signal mi32_rx_watch_drd      : std_logic_vector(31 downto 0);
   signal mi32_rx_watch_ardy     : std_logic;
   signal mi32_rx_watch_drdy     : std_logic;

   -- -------------------------------------------------------------------------
   --                        FrameLink signals
   -- -------------------------------------------------------------------------
   -- signals to FL_WATCH
   signal fl_watch_rx_sop_n     : std_logic_vector(1 downto 0);
   signal fl_watch_rx_eop_n     : std_logic_vector(1 downto 0);
   signal fl_watch_rx_sof_n     : std_logic_vector(1 downto 0);
   signal fl_watch_rx_eof_n     : std_logic_vector(1 downto 0);
   signal fl_watch_rx_src_rdy_n : std_logic_vector(1 downto 0);
   signal fl_watch_rx_dst_rdy_n : std_logic_vector(1 downto 0);

   signal fl_watch_tx_sop_n     : std_logic_vector(1 downto 0);
   signal fl_watch_tx_eop_n     : std_logic_vector(1 downto 0);
   signal fl_watch_tx_sof_n     : std_logic_vector(1 downto 0);
   signal fl_watch_tx_eof_n     : std_logic_vector(1 downto 0);
   signal fl_watch_tx_src_rdy_n : std_logic_vector(1 downto 0);
   signal fl_watch_tx_dst_rdy_n : std_logic_vector(1 downto 0);

   -- -------------------------------------------------------------------------
   --                         Pacodag signals
   -- -------------------------------------------------------------------------
   signal ts_sync               : std_logic_vector(63 downto 0);
   signal ts_dv_sync            : std_logic;

-- ----------------------------------------------------------------------------
--                             Architecture body
-- ----------------------------------------------------------------------------
begin

   -- -------------------------------------------------------------------------
   --                             FrameLink
   -- -------------------------------------------------------------------------
   -- NET 1 -> NET 0
   n12n0_tr: entity work.FL_TRIMMER
   generic map(
      DATA_WIDTH     => 128,
      -- information about frame --
      -- header is present in frame
      HEADER         => true,
      -- footer is present in frame
      FOOTER         => false,
      -- if true, header is trimmed
      TRIM_HEADER    => true,
      -- if true, footer is trimmed
      TRIM_FOOTER    => false
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      -- input interf
      RX_SOF_N       => IBUF1_TX_SOF_N,
      RX_SOP_N       => IBUF1_TX_SOP_N,
      RX_EOP_N       => IBUF1_TX_EOP_N,
      RX_EOF_N       => IBUF1_TX_EOF_N,
      RX_SRC_RDY_N   => IBUF1_TX_SRC_RDY_N,
      RX_DST_RDY_N   => IBUF1_TX_DST_RDY_N,
      RX_DATA        => IBUF1_TX_DATA,
      RX_REM         => IBUF1_TX_REM,
      
      -- output inter
      TX_SOF_N       => OBUF0_RX_SOF_N,
      TX_SOP_N       => OBUF0_RX_SOP_N,
      TX_EOP_N       => OBUF0_RX_EOP_N,
      TX_EOF_N       => OBUF0_RX_EOF_N,
      TX_SRC_RDY_N   => OBUF0_RX_SRC_RDY_N,
      TX_DST_RDY_N   => OBUF0_RX_DST_RDY_N,
      TX_DATA        => OBUF0_RX_DATA,
      TX_REM         => OBUF0_RX_REM,
      
      -- control sign
      ENABLE         => '1'
   );

   -- NET 0 -> NET 1
   n02n1_tr: entity work.FL_TRIMMER
   generic map(
      DATA_WIDTH     => 128,
      -- information about frame --
      -- header is present in frame
      HEADER         => true,
      -- footer is present in frame
      FOOTER         => false,
      -- if true, header is trimmed
      TRIM_HEADER    => true,
      -- if true, footer is trimmed
      TRIM_FOOTER    => false
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      -- input interf
      RX_SOF_N       => IBUF0_TX_SOF_N,
      RX_SOP_N       => IBUF0_TX_SOP_N,
      RX_EOP_N       => IBUF0_TX_EOP_N,
      RX_EOF_N       => IBUF0_TX_EOF_N,
      RX_SRC_RDY_N   => IBUF0_TX_SRC_RDY_N,
      RX_DST_RDY_N   => IBUF0_TX_DST_RDY_N,
      RX_DATA        => IBUF0_TX_DATA,
      RX_REM         => IBUF0_TX_REM,
      
      -- output inter
      TX_SOF_N       => OBUF1_RX_SOF_N,
      TX_SOP_N       => OBUF1_RX_SOP_N,
      TX_EOP_N       => OBUF1_RX_EOP_N,
      TX_EOF_N       => OBUF1_RX_EOF_N,
      TX_SRC_RDY_N   => OBUF1_RX_SRC_RDY_N,
      TX_DST_RDY_N   => OBUF1_RX_DST_RDY_N,
      TX_DATA        => OBUF1_RX_DATA,
      TX_REM         => OBUF1_RX_REM,
      
      -- control sign
      ENABLE         => '1'
   );

   -- null -> DMA 0
   TX0_DATA          <= X"00000000000000000000000000000000";
   TX0_DREM          <= "0000";
   TX0_SOF_N         <= '1';
   TX0_EOF_N         <= '1';
   TX0_SOP_N         <= '1';
   TX0_EOP_N         <= '1';
   TX0_SRC_RDY_N     <= '1';

   -- null -> DMA 1
   TX1_DATA          <= X"00000000000000000000000000000000";
   TX1_DREM          <= "0000";
   TX1_SOF_N         <= '1';
   TX1_EOF_N         <= '1';
   TX1_SOP_N         <= '1';
   TX1_EOP_N         <= '1';
   TX1_SRC_RDY_N     <= '1';

   -- DMA 0 -> null
   RX0_DST_RDY_N     <= '0';

   -- DMA 1 -> null  
   RX1_DST_RDY_N     <= '0';

   -- -------------------------------------------------------------------------
   --                                   IB
   -- -------------------------------------------------------------------------
   IB_UP_DATA <= X"0000000000000000";
   IB_UP_SOF_N <= '1';
   IB_UP_EOF_N <= '1';
   IB_UP_SRC_RDY_N <= '1';
   IB_DOWN_DST_RDY_N <= '0';

   -- -------------------------------------------------------------------------
   --                                   MI32
   -- -------------------------------------------------------------------------

   -- MI_SPLITTER for both FL_WATCH units
   MI_SPLITTER_I: entity work.MI_SPLITTER
   generic map(
      ITEMS      => 2,
      ADDR_WIDTH => 5,
      DATA_WIDTH => 32,
      PIPE       => false
   )
   port map(
      -- Common interface
      CLK      => CLK,
      RESET    => RESET,

      -- Input MI interface
      IN_DWR   => MI32_DWR,
      IN_ADDR  => MI32_ADDR(5 downto 0),
      IN_BE    => MI32_BE,
      IN_RD    => MI32_RD,
      IN_WR    => MI32_WR,
      IN_ARDY  => MI32_ARDY,
      IN_DRD   => MI32_DRD,
      IN_DRDY  => MI32_DRDY,

      -- Output MI interfaces
      OUT_DWR(31 downto 0)    => mi32_rx_watch_dwr,
      OUT_DWR(63 downto 32)   => mi32_tx_watch_dwr,
      OUT_ADDR(4 downto 0)    => mi32_rx_watch_addr(4 downto 0),
      OUT_ADDR(9 downto 5)    => mi32_tx_watch_addr(4 downto 0),
      OUT_BE(3 downto 0)      => mi32_rx_watch_be,
      OUT_BE(7 downto 4)      => mi32_tx_watch_be,
      OUT_RD(0)               => mi32_rx_watch_rd,
      OUT_RD(1)               => mi32_tx_watch_rd,
      OUT_WR(0)               => mi32_rx_watch_wr,
      OUT_WR(1)               => mi32_tx_watch_wr,
      OUT_ARDY(0)             => mi32_rx_watch_ardy,
      OUT_ARDY(1)             => mi32_tx_watch_ardy,
      OUT_DRD(31 downto 0)    => mi32_rx_watch_drd,
      OUT_DRD(63 downto 32)   => mi32_tx_watch_drd,
      OUT_DRDY(0)             => mi32_rx_watch_drdy,
      OUT_DRDY(1)             => mi32_tx_watch_drdy
   );

   -- FL_WATCH RX (ibuf->application)
   FL_WATCH_RX_I : FL_WATCH_2
   port map(
      CLK       => CLK,
      RESET     => RESET,

      SOF_N     => fl_watch_rx_sof_n,
      EOF_N     => fl_watch_rx_eof_n,
      SOP_N     => fl_watch_rx_sop_n,
      EOP_N     => fl_watch_rx_eop_n,
      DST_RDY_N => fl_watch_rx_dst_rdy_n,
      SRC_RDY_N => fl_watch_rx_src_rdy_n,

      MI_DWR    => mi32_rx_watch_dwr,
      MI_ADDR   => mi32_rx_watch_addr,
      MI_RD     => mi32_rx_watch_rd,
      MI_WR     => mi32_rx_watch_wr,
      MI_BE     => mi32_rx_watch_be,
      MI_DRD    => mi32_rx_watch_drd,
      MI_ARDY   => mi32_rx_watch_ardy,
      MI_DRDY   => mi32_rx_watch_drdy
   );

   fl_watch_rx_sof_n <= IBUF1_TX_SOF_N & IBUF0_TX_SOF_N;
   fl_watch_rx_eof_n <= IBUF1_TX_EOF_N & IBUF0_TX_EOF_N;
   fl_watch_rx_sop_n <= IBUF1_TX_SOP_N & IBUF0_TX_SOP_N;
   fl_watch_rx_eop_n <= IBUF1_TX_EOP_N & IBUF0_TX_EOP_N;
   fl_watch_rx_src_rdy_n <= IBUF1_TX_SRC_RDY_N & IBUF0_TX_SRC_RDY_N;
   fl_watch_rx_dst_rdy_n <= TX1_DST_RDY_N & TX0_DST_RDY_N;

   -- FL_WATCH TX (application->obuf)
   FL_WATCH_TX_I : FL_WATCH_2
   port map(
      CLK       => CLK,
      RESET     => RESET,

      SOF_N     => fl_watch_tx_sof_n,
      EOF_N     => fl_watch_tx_eof_n,
      SOP_N     => fl_watch_tx_sop_n,
      EOP_N     => fl_watch_tx_eop_n,
      DST_RDY_N => fl_watch_tx_dst_rdy_n,
      SRC_RDY_N => fl_watch_tx_src_rdy_n,

      MI_DWR    => mi32_tx_watch_dwr,
      MI_ADDR   => mi32_tx_watch_addr,
      MI_RD     => mi32_tx_watch_rd,
      MI_WR     => mi32_tx_watch_wr,
      MI_BE     => mi32_tx_watch_be, 
      MI_DRD    => mi32_tx_watch_drd, 
      MI_ARDY   => mi32_tx_watch_ardy, 
      MI_DRDY   => mi32_tx_watch_drdy 
   );

   fl_watch_tx_sof_n <= RX1_SOF_N & RX0_SOF_N;
   fl_watch_tx_eof_n <= RX1_EOF_N & RX0_EOF_N;
   fl_watch_tx_sop_n <= RX1_SOP_N & RX0_SOP_N;
   fl_watch_tx_eop_n <= RX1_EOP_N & RX0_EOP_N;
   fl_watch_tx_src_rdy_n <= RX1_SRC_RDY_N & RX0_SRC_RDY_N;
   fl_watch_tx_dst_rdy_n <= OBUF1_RX_DST_RDY_N & OBUF0_RX_DST_RDY_N;

   -- -------------------------------------------------------------------------
   --                              PACODAG
   -- -------------------------------------------------------------------------
   PACODAG_TOP_I: entity work.pacodag_tsu_top2_128b_norec
   generic map(
      HEADER_EN => PACODAG_HEADER_EN,
      FOOTER_EN => PACODAG_FOOTER_EN
   )
   port map(
      -- Common interface
      RESET    => RESET,
      -- IBUF interface
      PCD0_CTRL_CLK              => IBUF0_CTRL_CLK,
      PCD0_CTRL_DATA             => IBUF0_CTRL_DATA,
      PCD0_CTRL_REM              => IBUF0_CTRL_REM,
      PCD0_CTRL_SRC_RDY_N        => IBUF0_CTRL_SRC_RDY_N,
      PCD0_CTRL_SOP_N            => IBUF0_CTRL_SOP_N,
      PCD0_CTRL_EOP_N            => IBUF0_CTRL_EOP_N,
      PCD0_CTRL_DST_RDY_N        => IBUF0_CTRL_DST_RDY_N,
      PCD0_CTRL_RDY              => IBUF0_CTRL_RDY,
      PCD0_SOP                   => IBUF0_SOP,
      PCD0_STAT_PAYLOAD_LEN      => IBUF0_PAYLOAD_LEN,
      PCD0_STAT_FRAME_ERROR      => IBUF0_FRAME_ERROR,
      PCD0_STAT_CRC_CHECK_FAILED => IBUF0_CRC_CHECK_FAILED,
      PCD0_STAT_MAC_CHECK_FAILED => IBUF0_MAC_CHECK_FAILED,
      PCD0_STAT_LEN_BELOW_MIN    => IBUF0_LEN_BELOW_MIN,
      PCD0_STAT_LEN_OVER_MTU     => IBUF0_LEN_OVER_MTU,
      PCD0_STAT_DV               => IBUF0_STAT_DV,

      PCD1_CTRL_CLK              => IBUF1_CTRL_CLK,
      PCD1_CTRL_DATA             => IBUF1_CTRL_DATA,
      PCD1_CTRL_REM              => IBUF1_CTRL_REM,
      PCD1_CTRL_SRC_RDY_N        => IBUF1_CTRL_SRC_RDY_N,
      PCD1_CTRL_SOP_N            => IBUF1_CTRL_SOP_N,
      PCD1_CTRL_EOP_N            => IBUF1_CTRL_EOP_N,
      PCD1_CTRL_DST_RDY_N        => IBUF1_CTRL_DST_RDY_N,
      PCD1_CTRL_RDY              => IBUF1_CTRL_RDY,
      PCD1_SOP                   => IBUF1_SOP,
      PCD1_STAT_PAYLOAD_LEN      => IBUF1_PAYLOAD_LEN,
      PCD1_STAT_FRAME_ERROR      => IBUF1_FRAME_ERROR,
      PCD1_STAT_CRC_CHECK_FAILED => IBUF1_CRC_CHECK_FAILED,
      PCD1_STAT_MAC_CHECK_FAILED => IBUF1_MAC_CHECK_FAILED,
      PCD1_STAT_LEN_BELOW_MIN    => IBUF1_LEN_BELOW_MIN,
      PCD1_STAT_LEN_OVER_MTU     => IBUF1_LEN_OVER_MTU,
      PCD1_STAT_DV               => IBUF1_STAT_DV,

      TS       => ts_sync,
      TS_DV    => ts_dv_sync
   );

   tsu_async_i : tsu_async
   -- PORTS
   port map (
      RESET          => RESET,
      
      -- Input interface
      IN_CLK         => TS_CLK,
      
      IN_TS          => TS,
      IN_TS_DV       => TS_DV,
      
      -- Output interface
      OUT_CLK        => IBUF0_CTRL_CLK,
      
      OUT_TS         => ts_sync,
      OUT_TS_DV      => ts_dv_sync
   );

end architecture full;
