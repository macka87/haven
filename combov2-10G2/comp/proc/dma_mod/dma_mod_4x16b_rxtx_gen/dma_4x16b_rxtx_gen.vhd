-- dma_4x16b_rxtx_gen.vhd: DMA Module for 4x16 RX+TX interface
-- Copyright (C) 2008 CESNET
-- Author(s):  Pavol Korcek <korcek@liberouter.org>
--             Martin Kosek <kosek@liberouter.org>
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

use work.fl_pkg.all;
use work.ib_pkg.all; -- Internal bus package

use work.dma_mod_4x16b_rxtx_gen_const.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of DMA_MOD_4x16b_RXTX_GEN is

signal tr2mux_rx0_data     : std_logic_vector(63 downto 0);
signal tr2mux_rx0_drem     : std_logic_vector(2 downto 0);
signal tr2mux_rx0_sop_n    : std_logic;
signal tr2mux_rx0_eop_n    : std_logic;
signal tr2mux_rx0_sof_n    : std_logic;
signal tr2mux_rx0_eof_n    : std_logic;
signal tr2mux_rx0_src_rdy_n: std_logic;
signal tr2mux_rx0_dst_rdy_n: std_logic;

signal tr2mux_rx1_data     : std_logic_vector(63 downto 0);
signal tr2mux_rx1_drem     : std_logic_vector(2 downto 0);
signal tr2mux_rx1_sop_n    : std_logic;
signal tr2mux_rx1_eop_n    : std_logic;
signal tr2mux_rx1_sof_n    : std_logic;
signal tr2mux_rx1_eof_n    : std_logic;
signal tr2mux_rx1_src_rdy_n: std_logic;
signal tr2mux_rx1_dst_rdy_n: std_logic;

signal tr2mux_rx2_data     : std_logic_vector(63 downto 0);
signal tr2mux_rx2_drem     : std_logic_vector(2 downto 0);
signal tr2mux_rx2_sop_n    : std_logic;
signal tr2mux_rx2_eop_n    : std_logic;
signal tr2mux_rx2_sof_n    : std_logic;
signal tr2mux_rx2_eof_n    : std_logic;
signal tr2mux_rx2_src_rdy_n: std_logic;
signal tr2mux_rx2_dst_rdy_n: std_logic;

signal tr2mux_rx3_data     : std_logic_vector(63 downto 0);
signal tr2mux_rx3_drem     : std_logic_vector(2 downto 0);
signal tr2mux_rx3_sop_n    : std_logic;
signal tr2mux_rx3_eop_n    : std_logic;
signal tr2mux_rx3_sof_n    : std_logic;
signal tr2mux_rx3_eof_n    : std_logic;
signal tr2mux_rx3_src_rdy_n: std_logic;
signal tr2mux_rx3_dst_rdy_n: std_logic;

signal mux_sof_n : std_logic;
signal mux_sop_n : std_logic;
signal mux_eop_n : std_logic;
signal mux_eof_n : std_logic;
signal mux_src_rdy_n : std_logic;
signal mux_dst_rdy_n : std_logic_vector(3 downto 0);
signal mux_data : std_logic_vector(63 downto 0);
signal mux_drem : std_logic_vector(2 downto 0);

signal mux_channel : std_logic_vector(1 downto 0);

signal trans_tx0_sof_n : std_logic;
signal trans_tx1_sof_n : std_logic;
signal trans_tx2_sof_n : std_logic;
signal trans_tx3_sof_n : std_logic;
                      
signal trans_tx0_sop_n : std_logic;
signal trans_tx1_sop_n : std_logic;
signal trans_tx2_sop_n : std_logic;
signal trans_tx3_sop_n : std_logic;
                      
signal trans_tx0_eop_n : std_logic;
signal trans_tx1_eop_n : std_logic;
signal trans_tx2_eop_n : std_logic;
signal trans_tx3_eop_n : std_logic;
                      
signal trans_tx0_eof_n : std_logic;
signal trans_tx1_eof_n : std_logic;
signal trans_tx2_eof_n : std_logic;
signal trans_tx3_eof_n : std_logic;
                      
signal trans_tx0_src_rdy_n : std_logic;
signal trans_tx1_src_rdy_n : std_logic;
signal trans_tx2_src_rdy_n : std_logic;
signal trans_tx3_src_rdy_n : std_logic;
                      
signal trans_tx0_dst_rdy_n : std_logic;
signal trans_tx1_dst_rdy_n : std_logic;
signal trans_tx2_dst_rdy_n : std_logic;
signal trans_tx3_dst_rdy_n : std_logic;

signal trans_tx0_data : std_logic_vector(63 downto 0);
signal trans_tx1_data : std_logic_vector(63 downto 0);
signal trans_tx2_data : std_logic_vector(63 downto 0);
signal trans_tx3_data : std_logic_vector(63 downto 0);
                 
signal trans_tx0_drem : std_logic_vector(2 downto 0);
signal trans_tx1_drem : std_logic_vector(2 downto 0);
signal trans_tx2_drem : std_logic_vector(2 downto 0);
signal trans_tx3_drem : std_logic_vector(2 downto 0);

begin
   RXTX_BUFFERS_I : entity work.DMA_MODULE_GEN
      generic map(
         RX_IFC_COUNT            => RX_IFC_COUNT,
         RX_BUFFER_SIZE          => RX_BUFFER_SIZE,
         RX_FL_WIDTH             => RX_FL_WIDTH,

         TX_IFC_COUNT            => TX_IFC_COUNT,
         TX_BUFFER_SIZE          => TX_BUFFER_SIZE,
         TX_FL_WIDTH             => TX_FL_WIDTH,

         RX_DISCARD_EN           => RX_DISCARD_EN,

         -- DMA Controller generics
         DESC_BLOCK_SIZE            => DESC_BLOCK_SIZE,
         DESC_BASE_ADDR             => DESC_BASE_ADDR,

         IB_EP_CONNECTED_TO         => IB_EP_CONNECTED_TO,
         IB_EP_ENDPOINT_BASE        => IB_EP_ENDPOINT_BASE,
         IB_EP_ENDPOINT_LIMIT       => IB_EP_ENDPOINT_LIMIT,
         IB_EP_STRICT_ORDER         => IB_EP_STRICT_ORDER,
         IB_EP_DATA_REORDER         => IB_EP_DATA_REORDER,
         IB_EP_READ_IN_PROCESS      => IB_EP_READ_IN_PROCESS,
         IB_EP_INPUT_BUFFER_SIZE    => IB_EP_INPUT_BUFFER_SIZE,
         IB_EP_OUTPUT_BUFFER_SIZE   => IB_EP_OUTPUT_BUFFER_SIZE
      )
      port map(
         -- Common interface
         CLK            => CLK,
         RESET          => RESET,
         RX_INTERRUPT   => RX_INTERRUPT,
         TX_INTERRUPT   => TX_INTERRUPT,

         -- RX Buffer status signals
         RX_BUFFER_STATUS  => open,
         RX_BUFFER_FULL    => open,
         RX_BUFFER_EMPTY   => open,

         -- input FrameLink interface
         RX_SOF_N             => mux_sof_n,
         RX_SOP_N             => mux_sop_n,
         RX_EOP_N             => mux_eop_n,
         RX_EOF_N             => mux_eof_n,
         RX_SRC_RDY_N         => mux_src_rdy_n,
         RX_DST_RDY_N         => mux_dst_rdy_n,
         RX_DATA              => mux_data,
         RX_REM               => mux_drem,
         -- Determine channel
         RX_ADDR              => mux_channel,
   
         -- output FrameLink interface
         TX_SOF_N(0)             => trans_tx0_sof_n,
         TX_SOF_N(1)             => trans_tx1_sof_n,
         TX_SOF_N(2)             => trans_tx2_sof_n,
         TX_SOF_N(3)             => trans_tx3_sof_n,

         TX_SOP_N(0)             => trans_tx0_sop_n,
         TX_SOP_N(1)             => trans_tx1_sop_n,
         TX_SOP_N(2)             => trans_tx2_sop_n,
         TX_SOP_N(3)             => trans_tx3_sop_n,

         TX_EOP_N(0)             => trans_tx0_eop_n,
         TX_EOP_N(1)             => trans_tx1_eop_n,
         TX_EOP_N(2)             => trans_tx2_eop_n,
         TX_EOP_N(3)             => trans_tx3_eop_n,

         TX_EOF_N(0)             => trans_tx0_eof_n,
         TX_EOF_N(1)             => trans_tx1_eof_n,
         TX_EOF_N(2)             => trans_tx2_eof_n,
         TX_EOF_N(3)             => trans_tx3_eof_n,

         TX_SRC_RDY_N(0)         => trans_tx0_src_rdy_n,
         TX_SRC_RDY_N(1)         => trans_tx1_src_rdy_n,
         TX_SRC_RDY_N(2)         => trans_tx2_src_rdy_n,
         TX_SRC_RDY_N(3)         => trans_tx3_src_rdy_n,

         TX_DST_RDY_N(0)         => trans_tx0_dst_rdy_n,
         TX_DST_RDY_N(1)         => trans_tx1_dst_rdy_n,
         TX_DST_RDY_N(2)         => trans_tx2_dst_rdy_n,
         TX_DST_RDY_N(3)         => trans_tx3_dst_rdy_n,

         TX_DATA(63 downto  0)  => trans_tx0_data,
         TX_DATA(127 downto 64)  => trans_tx1_data,
         TX_DATA(191 downto 128)  => trans_tx2_data,
         TX_DATA(255 downto 192)  => trans_tx3_data,

         TX_REM(2 downto 0)      => trans_tx0_drem,
         TX_REM(5 downto 3)      => trans_tx1_drem,
         TX_REM(8 downto 6)      => trans_tx2_drem,
         TX_REM(11 downto 9)      => trans_tx3_drem,
   

         --+ Upstream InternalBus
         UP_DATA                     => IB_UP_DATA,
         UP_SOF_N                    => IB_UP_SOF_N,
         UP_EOF_N                    => IB_UP_EOF_N,
         UP_SRC_RDY_N                => IB_UP_SRC_RDY_N,
         UP_DST_RDY_N                => IB_UP_DST_RDY_N,

         --+ Downstream InternalBus
         DOWN_DATA                   => IB_DOWN_DATA,
         DOWN_SOF_N                  => IB_DOWN_SOF_N,
         DOWN_EOF_N                  => IB_DOWN_EOF_N,
         DOWN_SRC_RDY_N              => IB_DOWN_SRC_RDY_N,
         DOWN_DST_RDY_N              => IB_DOWN_DST_RDY_N,

         --+ MI32 Interface
         MI32_DWR                  => MI32_DWR,
         MI32_ADDR                 => MI32_ADDR,
         MI32_BE                   => MI32_BE,
         MI32_RD                   => MI32_RD,
         MI32_WR                   => MI32_WR,
         MI32_DRDY                 => MI32_DRDY,
         MI32_ARDY                 => MI32_ARDY,
         MI32_DRD                  => MI32_DRD
      );

      FL_TRANS_RX0 : entity work.FL_TRANSFORMER
      generic map(
         RX_DATA_WIDTH => 16,
         TX_DATA_WIDTH => 64
      )
      port map(
         CLK                  => CLK,
         RESET                => RESET,

         RX_SOF_N             => RX0_SOF_N,
         RX_SOP_N             => RX0_SOP_N,
         RX_EOP_N             => RX0_EOP_N,
         RX_EOF_N             => RX0_EOF_N,
         RX_SRC_RDY_N         => RX0_SRC_RDY_N,
         RX_DST_RDY_N         => RX0_DST_RDY_N,
         RX_DATA              => RX0_DATA,
         RX_REM               => RX0_DREM,
                                                      
         TX_SOF_N             => tr2mux_rx0_sof_n,
         TX_SOP_N             => tr2mux_rx0_sop_n,
         TX_EOP_N             => tr2mux_rx0_eop_n,
         TX_EOF_N             => tr2mux_rx0_eof_n,
         TX_SRC_RDY_N         => tr2mux_rx0_src_rdy_n,
         TX_DST_RDY_N         => tr2mux_rx0_dst_rdy_n,
         TX_DATA              => tr2mux_rx0_data,
         TX_REM               => tr2mux_rx0_drem
      );

      FL_TRANS_RX1 : entity work.FL_TRANSFORMER
      generic map(
         RX_DATA_WIDTH => 16,
         TX_DATA_WIDTH => 64
      )
      port map(
         CLK                  => CLK,
         RESET                => RESET,

         RX_SOF_N             => RX1_SOF_N,
         RX_SOP_N             => RX1_SOP_N,
         RX_EOP_N             => RX1_EOP_N,
         RX_EOF_N             => RX1_EOF_N,
         RX_SRC_RDY_N         => RX1_SRC_RDY_N,
         RX_DST_RDY_N         => RX1_DST_RDY_N,
         RX_DATA              => RX1_DATA,
         RX_REM               => RX1_DREM,
                                                      
         TX_SOF_N             => tr2mux_rx1_sof_n,
         TX_SOP_N             => tr2mux_rx1_sop_n,
         TX_EOP_N             => tr2mux_rx1_eop_n,
         TX_EOF_N             => tr2mux_rx1_eof_n,
         TX_SRC_RDY_N         => tr2mux_rx1_src_rdy_n,
         TX_DST_RDY_N         => tr2mux_rx1_dst_rdy_n,
         TX_DATA              => tr2mux_rx1_data,
         TX_REM               => tr2mux_rx1_drem
      );

      FL_TRANS_RX2 : entity work.FL_TRANSFORMER
      generic map(
         RX_DATA_WIDTH => 16,
         TX_DATA_WIDTH => 64
      )
      port map(
         CLK                  => CLK,
         RESET                => RESET,

         RX_SOF_N             => RX2_SOF_N,
         RX_SOP_N             => RX2_SOP_N,
         RX_EOP_N             => RX2_EOP_N,
         RX_EOF_N             => RX2_EOF_N,
         RX_SRC_RDY_N         => RX2_SRC_RDY_N,
         RX_DST_RDY_N         => RX2_DST_RDY_N,
         RX_DATA              => RX2_DATA,
         RX_REM               => RX2_DREM,
                                                      
         TX_SOF_N             => tr2mux_rx2_sof_n,
         TX_SOP_N             => tr2mux_rx2_sop_n,
         TX_EOP_N             => tr2mux_rx2_eop_n,
         TX_EOF_N             => tr2mux_rx2_eof_n,
         TX_SRC_RDY_N         => tr2mux_rx2_src_rdy_n,
         TX_DST_RDY_N         => tr2mux_rx2_dst_rdy_n,
         TX_DATA              => tr2mux_rx2_data,
         TX_REM               => tr2mux_rx2_drem
      );

      FL_TRANS_RX3 : entity work.FL_TRANSFORMER
      generic map(
         RX_DATA_WIDTH => 16,
         TX_DATA_WIDTH => 64
      )
      port map(
         CLK                  => CLK,
         RESET                => RESET,

         RX_SOF_N             => RX3_SOF_N,
         RX_SOP_N             => RX3_SOP_N,
         RX_EOP_N             => RX3_EOP_N,
         RX_EOF_N             => RX3_EOF_N,
         RX_SRC_RDY_N         => RX3_SRC_RDY_N,
         RX_DST_RDY_N         => RX3_DST_RDY_N,
         RX_DATA              => RX3_DATA,
         RX_REM               => RX3_DREM,
                                                      
         TX_SOF_N             => tr2mux_rx3_sof_n,
         TX_SOP_N             => tr2mux_rx3_sop_n,
         TX_EOP_N             => tr2mux_rx3_eop_n,
         TX_EOF_N             => tr2mux_rx3_eof_n,
         TX_SRC_RDY_N         => tr2mux_rx3_src_rdy_n,
         TX_DST_RDY_N         => tr2mux_rx3_dst_rdy_n,
         TX_DATA              => tr2mux_rx3_data,
         TX_REM               => tr2mux_rx3_drem
      );

      --* RX FL Multiplexer
      fl_mux_i : entity work.FL_MULTIPLEXER
      generic map(
         DATA_WIDTH     => 64,
         CHANNELS       => 4
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,

         -- Two regular input FrameLinks
         RX_SOF_N(0)             => tr2mux_rx0_sof_n,
         RX_SOF_N(1)             => tr2mux_rx1_sof_n,
         RX_SOF_N(2)             => tr2mux_rx2_sof_n,
         RX_SOF_N(3)             => tr2mux_rx3_sof_n,

         RX_SOP_N(0)             => tr2mux_rx0_sop_n,
         RX_SOP_N(1)             => tr2mux_rx1_sop_n,
         RX_SOP_N(2)             => tr2mux_rx2_sop_n,
         RX_SOP_N(3)             => tr2mux_rx3_sop_n,

         RX_EOP_N(0)             => tr2mux_rx0_eop_n,
         RX_EOP_N(1)             => tr2mux_rx1_eop_n,
         RX_EOP_N(2)             => tr2mux_rx2_eop_n,
         RX_EOP_N(3)             => tr2mux_rx3_eop_n,

         RX_EOF_N(0)             => tr2mux_rx0_eof_n,
         RX_EOF_N(1)             => tr2mux_rx1_eof_n,
         RX_EOF_N(2)             => tr2mux_rx2_eof_n,
         RX_EOF_N(3)             => tr2mux_rx3_eof_n,

         RX_SRC_RDY_N(0)         => tr2mux_rx0_src_rdy_n,
         RX_SRC_RDY_N(1)         => tr2mux_rx1_src_rdy_n,
         RX_SRC_RDY_N(2)         => tr2mux_rx2_src_rdy_n,
         RX_SRC_RDY_N(3)         => tr2mux_rx3_src_rdy_n,

         RX_DST_RDY_N(0)         => tr2mux_rx0_dst_rdy_n,
         RX_DST_RDY_N(1)         => tr2mux_rx1_dst_rdy_n,
         RX_DST_RDY_N(2)         => tr2mux_rx2_dst_rdy_n,
         RX_DST_RDY_N(3)         => tr2mux_rx3_dst_rdy_n,

         RX_DATA(63 downto  0)  => tr2mux_rx0_data,
         RX_DATA(127 downto 64)  => tr2mux_rx1_data,
         RX_DATA(191 downto 128)  => tr2mux_rx2_data,
         RX_DATA(255 downto 192)  => tr2mux_rx3_data,

         RX_DREM(2 downto 0)     => tr2mux_rx0_drem,
         RX_DREM(5 downto 3)     => tr2mux_rx1_drem,
         RX_DREM(8 downto 6)     => tr2mux_rx2_drem,
         RX_DREM(11 downto 9)     => tr2mux_rx3_drem,

         -- One output multiplexed FrameLink
         TX_SOF_N       => mux_sof_n,
         TX_EOP_N       => mux_eop_n,
         TX_SOP_N       => mux_sop_n,
         TX_EOF_N       => mux_eof_n,
         TX_SRC_RDY_N   => mux_src_rdy_n,
         TX_DATA        => mux_data,
         TX_DREM        => mux_drem,
         TX_DST_RDY_N   => mux_dst_rdy_n,
         --* Determines the number of active input channel
         TX_CHANNEL     => mux_channel
      );

   FL_TRANS_TX0 : entity FL_TRANSFORMER
   generic map(
      RX_DATA_WIDTH => 64,
      TX_DATA_WIDTH => 16
   )
   port map(
      CLK                  => CLK,
      RESET                => RESET,

      RX_SOF_N             => trans_tx0_sof_n,
      RX_SOP_N             => trans_tx0_sop_n,
      RX_EOP_N             => trans_tx0_eop_n,
      RX_EOF_N             => trans_tx0_eof_n,
      RX_SRC_RDY_N         => trans_tx0_src_rdy_n,
      RX_DST_RDY_N         => trans_tx0_dst_rdy_n,
      RX_DATA              => trans_tx0_data,
      RX_REM               => trans_tx0_drem,
                              
      TX_SOF_N             => TX0_SOF_N,
      TX_SOP_N             => TX0_SOP_N,
      TX_EOP_N             => TX0_EOP_N,
      TX_EOF_N             => TX0_EOF_N,
      TX_SRC_RDY_N         => TX0_SRC_RDY_N,
      TX_DST_RDY_N         => TX0_DST_RDY_N,
      TX_DATA              => TX0_DATA,
      TX_REM               => TX0_DREM
   );

   FL_TRANS_TX1 : entity FL_TRANSFORMER
   generic map(
      RX_DATA_WIDTH => 64,
      TX_DATA_WIDTH => 16
   )
   port map(
      CLK                  => CLK,
      RESET                => RESET,

      RX_SOF_N             => trans_tx1_sof_n,
      RX_SOP_N             => trans_tx1_sop_n,
      RX_EOP_N             => trans_tx1_eop_n,
      RX_EOF_N             => trans_tx1_eof_n,
      RX_SRC_RDY_N         => trans_tx1_src_rdy_n,
      RX_DST_RDY_N         => trans_tx1_dst_rdy_n,
      RX_DATA              => trans_tx1_data,
      RX_REM               => trans_tx1_drem,
                              
      TX_SOF_N             => TX1_SOF_N,
      TX_SOP_N             => TX1_SOP_N,
      TX_EOP_N             => TX1_EOP_N,
      TX_EOF_N             => TX1_EOF_N,
      TX_SRC_RDY_N         => TX1_SRC_RDY_N,
      TX_DST_RDY_N         => TX1_DST_RDY_N,
      TX_DATA              => TX1_DATA,
      TX_REM               => TX1_DREM
   );

   FL_TRANS_TX2 : entity FL_TRANSFORMER
   generic map(
      RX_DATA_WIDTH => 64,
      TX_DATA_WIDTH => 16
   )
   port map(
      CLK                  => CLK,
      RESET                => RESET,

      RX_SOF_N             => trans_tx2_sof_n,
      RX_SOP_N             => trans_tx2_sop_n,
      RX_EOP_N             => trans_tx2_eop_n,
      RX_EOF_N             => trans_tx2_eof_n,
      RX_SRC_RDY_N         => trans_tx2_src_rdy_n,
      RX_DST_RDY_N         => trans_tx2_dst_rdy_n,
      RX_DATA              => trans_tx2_data,
      RX_REM               => trans_tx2_drem,
                              
      TX_SOF_N             => TX2_SOF_N,
      TX_SOP_N             => TX2_SOP_N,
      TX_EOP_N             => TX2_EOP_N,
      TX_EOF_N             => TX2_EOF_N,
      TX_SRC_RDY_N         => TX2_SRC_RDY_N,
      TX_DST_RDY_N         => TX2_DST_RDY_N,
      TX_DATA              => TX2_DATA,
      TX_REM               => TX2_DREM
   );

   FL_TRANS_TX3 : entity FL_TRANSFORMER
   generic map(
      RX_DATA_WIDTH => 64,
      TX_DATA_WIDTH => 16
   )
   port map(
      CLK                  => CLK,
      RESET                => RESET,

      RX_SOF_N             => trans_tx3_sof_n,
      RX_SOP_N             => trans_tx3_sop_n,
      RX_EOP_N             => trans_tx3_eop_n,
      RX_EOF_N             => trans_tx3_eof_n,
      RX_SRC_RDY_N         => trans_tx3_src_rdy_n,
      RX_DST_RDY_N         => trans_tx3_dst_rdy_n,
      RX_DATA              => trans_tx3_data,
      RX_REM               => trans_tx3_drem,
                              
      TX_SOF_N             => TX3_SOF_N,
      TX_SOP_N             => TX3_SOP_N,
      TX_EOP_N             => TX3_EOP_N,
      TX_EOF_N             => TX3_EOF_N,
      TX_SRC_RDY_N         => TX3_SRC_RDY_N,
      TX_DST_RDY_N         => TX3_DST_RDY_N,
      TX_DATA              => TX3_DATA,
      TX_REM               => TX3_DREM
   );

end architecture;
-- ----------------------------------------------------------------------------
