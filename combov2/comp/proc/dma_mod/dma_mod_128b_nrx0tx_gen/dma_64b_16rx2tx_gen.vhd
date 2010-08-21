-- dma_64b_16rx2tx.vhd: DMA Module for 64 16RX+2TX interface
-- Copyright (C) 2008 CESNET
-- Author(s):  Viktor Pus <pus@liberouter.org>
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

use work.dma_mod_128b_nrx0tx_gen_const.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of dma_mod_128b_nrx0tx_gen is

   -- --------------- Local Bus Endpoint -----------------------------------
   constant LB_BASE_ADDR            :  std_logic_vector(31 downto 0) := X"00000800";
   constant LB_LIMIT                :  std_logic_vector(31 downto 0) := X"00000800";
   constant LB_FREQUENCY            :  integer := 100;
   constant LB_BUFFER_EN            :  boolean := false;

   constant DMA_SIZE          : integer := RX_FL_WIDTH;
   constant DMA_REM_SIZE      : integer := log2(DMA_SIZE/8);

   signal fl_pipe_transformer_input_rx_data     : std_logic_vector(RX_IFC_COUNT*FL_WIDTH-1 downto 0);
   signal fl_pipe_transformer_input_rx_drem     : std_logic_vector(RX_IFC_COUNT*FL_REM_WIDTH-1 downto 0);
   signal fl_pipe_transformer_input_rx_sop_n    : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal fl_pipe_transformer_input_rx_eop_n    : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal fl_pipe_transformer_input_rx_sof_n    : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal fl_pipe_transformer_input_rx_eof_n    : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal fl_pipe_transformer_input_rx_src_rdy_n: std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal fl_pipe_transformer_input_rx_dst_rdy_n: std_logic_vector(RX_IFC_COUNT-1 downto 0);

   signal fl_pipe_transformer_input_tx_data     : std_logic_vector(RX_IFC_COUNT*FL_WIDTH-1 downto 0);
   signal fl_pipe_transformer_input_tx_drem     : std_logic_vector(RX_IFC_COUNT*FL_REM_WIDTH-1 downto 0);
   signal fl_pipe_transformer_input_tx_sop_n    : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal fl_pipe_transformer_input_tx_eop_n    : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal fl_pipe_transformer_input_tx_sof_n    : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal fl_pipe_transformer_input_tx_eof_n    : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal fl_pipe_transformer_input_tx_src_rdy_n: std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal fl_pipe_transformer_input_tx_dst_rdy_n: std_logic_vector(RX_IFC_COUNT-1 downto 0);

   signal fl_pipe_transformer_output_rx_data     : std_logic_vector(RX_IFC_COUNT*DMA_SIZE-1 downto 0);
   signal fl_pipe_transformer_output_rx_drem     : std_logic_vector(RX_IFC_COUNT*DMA_REM_SIZE-1 downto 0);
   signal fl_pipe_transformer_output_rx_sop_n    : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal fl_pipe_transformer_output_rx_eop_n    : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal fl_pipe_transformer_output_rx_sof_n    : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal fl_pipe_transformer_output_rx_eof_n    : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal fl_pipe_transformer_output_rx_src_rdy_n: std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal fl_pipe_transformer_output_rx_dst_rdy_n: std_logic_vector(RX_IFC_COUNT-1 downto 0);

   signal fl_pipe_transformer_output_tx_data     : std_logic_vector(RX_IFC_COUNT*DMA_SIZE-1 downto 0);
   signal fl_pipe_transformer_output_tx_drem     : std_logic_vector(RX_IFC_COUNT*DMA_REM_SIZE-1 downto 0);
   signal fl_pipe_transformer_output_tx_sop_n    : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal fl_pipe_transformer_output_tx_eop_n    : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal fl_pipe_transformer_output_tx_sof_n    : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal fl_pipe_transformer_output_tx_eof_n    : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal fl_pipe_transformer_output_tx_src_rdy_n: std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal fl_pipe_transformer_output_tx_dst_rdy_n: std_logic_vector(RX_IFC_COUNT-1 downto 0);

   signal fl_dma_module_gen_rx_data     : std_logic_vector(DMA_SIZE-1 downto 0);
   signal fl_dma_module_gen_rx_drem     : std_logic_vector(DMA_REM_SIZE-1 downto 0);
   signal fl_dma_module_gen_rx_sop_n    : std_logic;
   signal fl_dma_module_gen_rx_eop_n    : std_logic;
   signal fl_dma_module_gen_rx_sof_n    : std_logic;
   signal fl_dma_module_gen_rx_eof_n    : std_logic;
   signal fl_dma_module_gen_rx_src_rdy_n: std_logic;
   signal fl_dma_module_gen_rx_dst_rdy_n: std_logic_vector(RX_IFC_COUNT-1 downto 0);

   signal fl_dma_module_gen_rx_addr     : std_logic_vector(log2(RX_IFC_COUNT)-1 downto 0);

   signal mi32_int_dwr                  : std_logic_vector(31 downto 0);
   signal mi32_int_addr                 : std_logic_vector(31 downto 0);
   signal mi32_int_be                   : std_logic_vector(3 downto 0);
   signal mi32_int_rd                   : std_logic;
   signal mi32_int_wr                   : std_logic;
   signal mi32_int_drdy                 : std_logic;
   signal mi32_int_ardy                 : std_logic;
   signal mi32_int_drd                  : std_logic_vector(31 downto 0);

   -- GICS signals
   signal gics_int_down_data         : std_logic_vector(DMA_SIZE-1 downto 0);
   signal gics_int_down_sof_n        : std_logic;
   signal gics_int_down_eof_n        : std_logic;
   signal gics_int_down_src_rdy_n    : std_logic;
   signal gics_int_down_dst_rdy_n    : std_logic;

   signal gics_int_up_data        : std_logic_vector(DMA_SIZE-1 downto 0);
   signal gics_int_up_sof_n       : std_logic;
   signal gics_int_up_eof_n       : std_logic;
   signal gics_int_up_src_rdy_n   : std_logic;
   signal gics_int_up_dst_rdy_n   : std_logic;

begin
   --* DMA module
   RXTX_BUFFERS_I : entity work.dma_module_gen
      generic map(
         -- number of network interfaces
         RX_IFC_COUNT               => RX_IFC_COUNT,
         RX_BUFFER_SIZE             => RX_BUFFER_SIZE,
         RX_FL_WIDTH                => RX_FL_WIDTH,

         TX_IFC_COUNT               => TX_IFC_COUNT,
         TX_BUFFER_SIZE             => TX_BUFFER_SIZE,
         TX_FL_WIDTH                => TX_FL_WIDTH,
         -- Discard
         RX_DISCARD_EN              => RX_DISCARD_EN,
         -- DMA Controller generics
         DESC_BLOCK_SIZE            => DESC_BLOCK_SIZE,
         DESC_BASE_ADDR             => DESC_BASE_ADDR,
         -- Internal Bus Endpoint generics
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
         RX_SOF_N             => fl_dma_module_gen_rx_sof_n,
         RX_SOP_N             => fl_dma_module_gen_rx_sop_n,
         RX_EOP_N             => fl_dma_module_gen_rx_eop_n,
         RX_EOF_N             => fl_dma_module_gen_rx_eof_n,
         RX_SRC_RDY_N         => fl_dma_module_gen_rx_src_rdy_n,
         RX_DST_RDY_N         => fl_dma_module_gen_rx_dst_rdy_n,
         RX_DATA              => fl_dma_module_gen_rx_data,
         RX_REM               => fl_dma_module_gen_rx_drem,
         -- Determine channel
         RX_ADDR              => fl_dma_module_gen_rx_addr,

         -- output FrameLink interface
         TX_SOF_N(0)             => open,
         TX_SOF_N(1)             => open,
         TX_SOP_N(0)             => open,
         TX_SOP_N(1)             => open,
         TX_EOP_N(0)             => open,
         TX_EOP_N(1)             => open,
         TX_EOF_N(0)             => open,
         TX_EOF_N(1)             => open,
         TX_SRC_RDY_N(0)         => open,
         TX_SRC_RDY_N(1)         => open,
         TX_DST_RDY_N(0)         => '1',
         TX_DST_RDY_N(1)         => '1',
         TX_DATA( 63 downto  0)  => open,
         TX_DATA(127 downto 64)  => open,
         TX_REM(2 downto 0)      => open,
         TX_REM(5 downto 3)      => open,
      
         --+ Upstream InternalBus
         UP_DATA                     => gics_int_up_data,
         UP_SOF_N                    => gics_int_up_sof_n,
         UP_EOF_N                    => gics_int_up_eof_n,
         UP_SRC_RDY_N                => gics_int_up_src_rdy_n,
         UP_DST_RDY_N                => gics_int_up_dst_rdy_n,
     
         --+ Downstream InternalBus
         DOWN_DATA                   => gics_int_down_data,
         DOWN_SOF_N                  => gics_int_down_sof_n,
         DOWN_EOF_N                  => gics_int_down_eof_n,
         DOWN_SRC_RDY_N              => gics_int_down_src_rdy_n,
         DOWN_DST_RDY_N              => gics_int_down_dst_rdy_n,

         --+ MI32 Interface
         MI32_DWR                  => mi32_int_dwr,
         MI32_ADDR                 => mi32_int_addr,
         MI32_BE                   => mi32_int_be,
         MI32_RD                   => mi32_int_rd,
         MI32_WR                   => mi32_int_wr,
         MI32_DRDY                 => mi32_int_drdy,
         MI32_ARDY                 => mi32_int_ardy,
         MI32_DRD                  => mi32_int_drd
      );

   -- -------------------------------------------------------------------------
   --  Domain transfer ICS -> USER
   -- -------------------------------------------------------------------------

   asfifo_gen: for i in 0 to RX_IFC_COUNT-1 generate
      FL_ASYNC_RX : entity work.fl_asfifo_cv2_128b
         port map(
            RX_CLK      => USER_CLK,
            RX_RESET    => USER_RESET,
            TX_CLK      => CLK,
            TX_RESET    => RESET,

            RX_DATA     => RX_DATA((i+1)*FL_WIDTH-1 downto i*FL_WIDTH),
            RX_REM      => RX_DREM((i+1)*FL_REM_WIDTH-1 downto i*FL_REM_WIDTH),
            RX_EOP_N    => RX_EOP_N(i),
            RX_SOP_N    => RX_SOP_N(i),
            RX_EOF_N    => RX_EOF_N(i),
            RX_SOF_N    => RX_SOF_N(i),
            RX_SRC_RDY_N=> RX_SRC_RDY_N(i),
            RX_DST_RDY_N=> RX_DST_RDY_N(i),

            TX_DATA     => fl_pipe_transformer_input_rx_data((i+1)*FL_WIDTH-1 downto i*FL_WIDTH),
            TX_REM      => fl_pipe_transformer_input_rx_drem((i+1)*FL_REM_WIDTH-1 downto i*FL_REM_WIDTH),
            TX_EOP_N    => fl_pipe_transformer_input_rx_eop_n(i),
            TX_SOP_N    => fl_pipe_transformer_input_rx_sop_n(i),
            TX_EOF_N    => fl_pipe_transformer_input_rx_eof_n(i),
            TX_SOF_N    => fl_pipe_transformer_input_rx_sof_n(i),
            TX_SRC_RDY_N=> fl_pipe_transformer_input_rx_src_rdy_n(i),
            TX_DST_RDY_N=> fl_pipe_transformer_input_rx_dst_rdy_n(i)
         );
   end generate;

   -- -------------------------------------------------------------------------
   --  Data width transforming and pipelining to improve timing
   -- -------------------------------------------------------------------------

   transform_gen: for i in 0 to RX_IFC_COUNT-1 generate
      FL_PIPE_INPUT_I: entity work.FL_PIPE
         generic map(
            DATA_WIDTH     => FL_WIDTH,
            USE_OUTREG     => true
         )
         port map(
            -- Common interface 
            CLK            => CLK,
            RESET          => RESET,

            -- Input interface
            RX_SOF_N       => fl_pipe_transformer_input_rx_sof_n(i),
            RX_SOP_N       => fl_pipe_transformer_input_rx_sop_n(i),
            RX_EOP_N       => fl_pipe_transformer_input_rx_eop_n(i),
            RX_EOF_N       => fl_pipe_transformer_input_rx_eof_n(i),
            RX_SRC_RDY_N   => fl_pipe_transformer_input_rx_src_rdy_n(i),
            RX_DST_RDY_N   => fl_pipe_transformer_input_rx_dst_rdy_n(i),
            RX_DATA        => fl_pipe_transformer_input_rx_data((i+1)*FL_WIDTH-1 downto i*FL_WIDTH),
            RX_REM         => fl_pipe_transformer_input_rx_drem((i+1)*FL_REM_WIDTH-1 downto i*FL_REM_WIDTH),

            -- Output interface
            TX_SOF_N       => fl_pipe_transformer_input_tx_sof_n(i),
            TX_EOP_N       => fl_pipe_transformer_input_tx_eop_n(i),
            TX_SOP_N       => fl_pipe_transformer_input_tx_sop_n(i),
            TX_EOF_N       => fl_pipe_transformer_input_tx_eof_n(i),
            TX_SRC_RDY_N   => fl_pipe_transformer_input_tx_src_rdy_n(i),
            TX_DST_RDY_N   => fl_pipe_transformer_input_tx_dst_rdy_n(i),
            TX_DATA        => fl_pipe_transformer_input_tx_data((i+1)*FL_WIDTH-1 downto i*FL_WIDTH),
            TX_REM         => fl_pipe_transformer_input_tx_drem((i+1)*FL_REM_WIDTH-1 downto i*FL_REM_WIDTH)
         );

      FL_TRANSFORMER_I: entity work.FL_TRANSFORMER
         generic map (
            RX_DATA_WIDTH  => FL_WIDTH,
            TX_DATA_WIDTH  => DMA_SIZE
         )
         port map (
            CLK            => CLK,
            RESET          => RESET,

            -- RX interface
            RX_DATA        => fl_pipe_transformer_input_tx_data((i+1)*FL_WIDTH-1 downto i*FL_WIDTH),
            RX_REM         => fl_pipe_transformer_input_tx_drem((i+1)*FL_REM_WIDTH-1 downto i*FL_REM_WIDTH),
            RX_SOF_N       => fl_pipe_transformer_input_tx_sof_n(i),
            RX_SOP_N       => fl_pipe_transformer_input_tx_sop_n(i),
            RX_EOP_N       => fl_pipe_transformer_input_tx_eop_n(i),
            RX_EOF_N       => fl_pipe_transformer_input_tx_eof_n(i),
            RX_SRC_RDY_N   => fl_pipe_transformer_input_tx_src_rdy_n(i),
            RX_DST_RDY_N   => fl_pipe_transformer_input_tx_dst_rdy_n(i),

            -- TX interface
            TX_DATA        => fl_pipe_transformer_output_rx_data((i+1)*DMA_SIZE-1 downto i*DMA_SIZE),
            TX_REM         => fl_pipe_transformer_output_rx_drem((i+1)*DMA_REM_SIZE-1 downto i*DMA_REM_SIZE),
            TX_SOF_N       => fl_pipe_transformer_output_rx_sof_n(i),
            TX_SOP_N       => fl_pipe_transformer_output_rx_sop_n(i),
            TX_EOP_N       => fl_pipe_transformer_output_rx_eop_n(i),
            TX_EOF_N       => fl_pipe_transformer_output_rx_eof_n(i),
            TX_SRC_RDY_N   => fl_pipe_transformer_output_rx_src_rdy_n(i),
            TX_DST_RDY_N   => fl_pipe_transformer_output_rx_dst_rdy_n(i)
         );


      FL_PIPE_OUTPUT_I: entity work.FL_PIPE
         generic map(
            DATA_WIDTH     => DMA_SIZE,
            USE_OUTREG     => true
         )
         port map(
            -- Common interface 
            CLK            => CLK,
            RESET          => RESET,

            -- Input interface
            RX_SOF_N       => fl_pipe_transformer_output_rx_sof_n(i),
            RX_SOP_N       => fl_pipe_transformer_output_rx_sop_n(i),
            RX_EOP_N       => fl_pipe_transformer_output_rx_eop_n(i),
            RX_EOF_N       => fl_pipe_transformer_output_rx_eof_n(i),
            RX_SRC_RDY_N   => fl_pipe_transformer_output_rx_src_rdy_n(i),
            RX_DST_RDY_N   => fl_pipe_transformer_output_rx_dst_rdy_n(i),
            RX_DATA        => fl_pipe_transformer_output_rx_data((i+1)*DMA_SIZE-1 downto i*DMA_SIZE),
            RX_REM         => fl_pipe_transformer_output_rx_drem((i+1)*DMA_REM_SIZE-1 downto i*DMA_REM_SIZE),

            -- Output interface
            TX_SOF_N       => fl_pipe_transformer_output_tx_sof_n(i),
            TX_EOP_N       => fl_pipe_transformer_output_tx_eop_n(i),
            TX_SOP_N       => fl_pipe_transformer_output_tx_sop_n(i),
            TX_EOF_N       => fl_pipe_transformer_output_tx_eof_n(i),
            TX_SRC_RDY_N   => fl_pipe_transformer_output_tx_src_rdy_n(i),
            TX_DST_RDY_N   => fl_pipe_transformer_output_tx_dst_rdy_n(i),
            TX_DATA        => fl_pipe_transformer_output_tx_data((i+1)*DMA_SIZE-1 downto i*DMA_SIZE),
            TX_REM         => fl_pipe_transformer_output_tx_drem((i+1)*DMA_REM_SIZE-1 downto i*DMA_REM_SIZE)
         );

   end generate;


   -- -------------------------------------------------------------------------
   --  FL Multiplexer
   -- -------------------------------------------------------------------------

   flmuxi: entity work.FL_MULTIPLEXER
      generic map(
         --* FrameLink data width
         DATA_WIDTH     => DMA_SIZE,
         --* Number of FrameLink channels
         CHANNELS       => RX_IFC_COUNT
      )
      port map(
         --+ Common interface
         CLK            => CLK,
         RESET          => RESET,

         --+ Input FrameLink interface
         RX_SOF_N       => fl_pipe_transformer_output_tx_sof_n,
         RX_EOP_N       => fl_pipe_transformer_output_tx_eop_n,
         RX_SOP_N       => fl_pipe_transformer_output_tx_sop_n,
         RX_EOF_N       => fl_pipe_transformer_output_tx_eof_n,
         RX_SRC_RDY_N   => fl_pipe_transformer_output_tx_src_rdy_n,
         RX_DST_RDY_N   => fl_pipe_transformer_output_tx_dst_rdy_n,
         RX_DATA        => fl_pipe_transformer_output_tx_data,
         RX_DREM        => fl_pipe_transformer_output_tx_drem,

         --+ Output FrameLink interface
         TX_SOF_N       => fl_dma_module_gen_rx_sof_n,
         TX_SOP_N       => fl_dma_module_gen_rx_sop_n,
         TX_EOP_N       => fl_dma_module_gen_rx_eop_n,
         TX_EOF_N       => fl_dma_module_gen_rx_eof_n,
         TX_SRC_RDY_N   => fl_dma_module_gen_rx_src_rdy_n,
         TX_DST_RDY_N   => fl_dma_module_gen_rx_dst_rdy_n,
         TX_DATA        => fl_dma_module_gen_rx_data,
         TX_DREM        => fl_dma_module_gen_rx_drem,
         --* Determines the number of active input channel
         TX_CHANNEL     => fl_dma_module_gen_rx_addr
      );

   -- -------------------------------------------------------------------------
   --  LB endpoint
   -- -------------------------------------------------------------------------

   XGMII_REPEATER_LB_ENDPOINT_I: entity work.LB_ENDPOINT_NOREC
      generic map(
         BASE_ADDR      => LB_BASE_ADDR,
         LIMIT          => LB_LIMIT,
         FREQUENCY      => LB_FREQUENCY,
         BUFFER_EN      => LB_BUFFER_EN
      )
      port map(
         -- Common Interface
         RESET          => RESET,
         LB_CLK         => CLK,

         -- Local Bus Interface
         LB_DWR         => LB_DWR,
         LB_BE          => LB_BE,
         LB_ADS_N       => LB_ADS_N,
         LB_RD_N        => LB_RD_N,
         LB_WR_N        => LB_WR_N,
         LB_DRD         => LB_DRD,
         LB_RDY_N       => LB_RDY_N,
         LB_ERR_N       => LB_ERR_N,
         LB_ABORT_N     => LB_ABORT_N,

         -- User Component Interface
         CLK           => CLK,
         MI32_DWR      => mi32_int_dwr,
         MI32_ADDR     => mi32_int_addr,
         MI32_RD       => mi32_int_rd,
         MI32_WR       => mi32_int_wr,
         MI32_BE       => mi32_int_be,
         MI32_DRD      => mi32_int_drd,
         MI32_ARDY     => mi32_int_ardy,
         MI32_DRDY     => mi32_int_drdy
      );

   -- -------------------------------------------------------------------------
   --  ICS -> GICS conversion
   -- -------------------------------------------------------------------------

   ics2gicsi: entity work.ICS2GICS
      generic map(
         -- Data Width (min 16)
         DATA_WIDTH        => DMA_SIZE
      )
      port map(
         -- Common interface -----------------------------------------------------
         CLK               => CLK,
         RESET             => RESET,

         -- ICS interface --------------------------------------------------------
         ICS_IN_DATA         => IB_DOWN_DATA,
         ICS_IN_SOF_N        => IB_DOWN_SOF_N,
         ICS_IN_EOF_N        => IB_DOWN_EOF_N,
         ICS_IN_SRC_RDY_N    => IB_DOWN_SRC_RDY_N,
         ICS_IN_DST_RDY_N    => IB_DOWN_DST_RDY_N,

         ICS_OUT_DATA        => IB_UP_DATA,
         ICS_OUT_SOF_N       => IB_UP_SOF_N,
         ICS_OUT_EOF_N       => IB_UP_EOF_N,
         ICS_OUT_SRC_RDY_N   => IB_UP_SRC_RDY_N,
         ICS_OUT_DST_RDY_N   => IB_UP_DST_RDY_N,

         -- GICS interface -------------------------------------------------------
         GICS_IN_DATA         => gics_int_up_data,
         GICS_IN_SOF_N        => gics_int_up_sof_n,
         GICS_IN_EOF_N        => gics_int_up_eof_n,
         GICS_IN_SRC_RDY_N    => gics_int_up_src_rdy_n,
         GICS_IN_DST_RDY_N    => gics_int_up_dst_rdy_n,

         GICS_OUT_DATA        => gics_int_down_data,
         GICS_OUT_SOF_N       => gics_int_down_sof_n,
         GICS_OUT_EOF_N       => gics_int_down_eof_n,
         GICS_OUT_SRC_RDY_N   => gics_int_down_src_rdy_n,
         GICS_OUT_DST_RDY_N   => gics_int_down_dst_rdy_n
      );

end architecture;
-- ----------------------------------------------------------------------------
