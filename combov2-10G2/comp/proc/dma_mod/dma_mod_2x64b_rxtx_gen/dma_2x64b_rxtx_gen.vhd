-- dma_2x64b_rxtx.vhd: DMA Module for 2x64 RX+TX interface
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

use work.dma_mod_2x64b_rxtx_gen_const.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of DMA_MOD_2x64b_RXTX_GEN is

signal mux_data     : std_logic_vector(63 downto 0);
signal mux_drem     : std_logic_vector(2 downto 0);
signal mux_sop_n    : std_logic;
signal mux_eop_n    : std_logic;
signal mux_sof_n    : std_logic;
signal mux_eof_n    : std_logic;
signal mux_src_rdy_n: std_logic;
signal mux_dst_rdy_n: std_logic_vector(1 downto 0);
signal mux_channel  : std_logic_vector(0 downto 0);

begin
   --* DMA module
   RXTX_BUFFERS_I : entity work.dma_module_gen
      generic map(
         RX_IFC_COUNT               => RX_IFC_COUNT,
         RX_BUFFER_SIZE             => RX_BUFFER_SIZE,
         RX_FL_WIDTH                => RX_FL_WIDTH,

         TX_IFC_COUNT               => TX_IFC_COUNT,
         TX_BUFFER_SIZE             => TX_BUFFER_SIZE,
         TX_FL_WIDTH                => TX_FL_WIDTH,

         RX_DISCARD_EN              => RX_DISCARD_EN,
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
         TX_SOF_N(0)             => TX0_SOF_N,
         TX_SOF_N(1)             => TX1_SOF_N,

         TX_SOP_N(0)             => TX0_SOP_N,
         TX_SOP_N(1)             => TX1_SOP_N,

         TX_EOP_N(0)             => TX0_EOP_N,
         TX_EOP_N(1)             => TX1_EOP_N,

         TX_EOF_N(0)             => TX0_EOF_N,
         TX_EOF_N(1)             => TX1_EOF_N,

         TX_SRC_RDY_N(0)         => TX0_SRC_RDY_N,
         TX_SRC_RDY_N(1)         => TX1_SRC_RDY_N,

         TX_DST_RDY_N(0)         => TX0_DST_RDY_N,
         TX_DST_RDY_N(1)         => TX1_DST_RDY_N,

         TX_DATA( 63 downto  0)  => TX0_DATA,
         TX_DATA(127 downto 64)  => TX1_DATA,

         TX_REM(2 downto 0)      => TX0_DREM,
         TX_REM(5 downto 3)      => TX1_DREM,
      
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

      --* RX FL Multiplexer
      fl_mux_i : entity work.FL_MULTIPLEXER
      generic map(
         DATA_WIDTH     => 64,
         CHANNELS       => 2
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,

         -- Two regular input FrameLinks
         RX_SOF_N(0)             => RX0_SOF_N,
         RX_SOF_N(1)             => RX1_SOF_N,

         RX_SOP_N(0)             => RX0_SOP_N,
         RX_SOP_N(1)             => RX1_SOP_N,

         RX_EOP_N(0)             => RX0_EOP_N,
         RX_EOP_N(1)             => RX1_EOP_N,

         RX_EOF_N(0)             => RX0_EOF_N,
         RX_EOF_N(1)             => RX1_EOF_N,

         RX_SRC_RDY_N(0)         => RX0_SRC_RDY_N,
         RX_SRC_RDY_N(1)         => RX1_SRC_RDY_N,

         RX_DST_RDY_N(0)         => RX0_DST_RDY_N,
         RX_DST_RDY_N(1)         => RX1_DST_RDY_N,

         RX_DATA( 63 downto  0)  => RX0_DATA,
         RX_DATA(127 downto 64)  => RX1_DATA,

         RX_DREM(2 downto 0)     => RX0_DREM,
         RX_DREM(5 downto 3)     => RX1_DREM,

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

end architecture;
-- ----------------------------------------------------------------------------
