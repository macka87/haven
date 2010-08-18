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

use work.fl_pkg.all;

use work.dma_mod_2x64b_rxtx_const.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of DMA_MOD_2x64b_RXTX is

signal ics_rx0_data     : std_logic_vector(63 downto 0);
signal ics_rx0_drem     : std_logic_vector(2 downto 0);
signal ics_rx0_sop_n    : std_logic;
signal ics_rx0_eop_n    : std_logic;
signal ics_rx0_sof_n    : std_logic;
signal ics_rx0_eof_n    : std_logic;
signal ics_rx0_src_rdy_n: std_logic;
signal ics_rx0_dst_rdy_n: std_logic;

signal fl_async_rx0_input_pipe_in_data       : std_logic_vector((64+3+1+1+1+1)-1 downto 0);
signal fl_async_rx0_input_pipe_in_src_rdy    : std_logic;
signal fl_async_rx0_input_pipe_in_dst_rdy    : std_logic;
signal fl_async_rx0_input_pipe_in_src_rdy_n  : std_logic;
signal fl_async_rx0_input_pipe_in_dst_rdy_n  : std_logic;
signal fl_async_rx0_input_pipe_out_data      : std_logic_vector((64+3+1+1+1+1)-1 downto 0);
signal fl_async_rx0_input_pipe_out_src_rdy   : std_logic;
signal fl_async_rx0_input_pipe_out_dst_rdy   : std_logic;
signal fl_async_rx0_input_pipe_out_src_rdy_n : std_logic;
signal fl_async_rx0_input_pipe_out_dst_rdy_n : std_logic;

signal fl_async_rx0_output_pipe_in_data       : std_logic_vector((64+3+1+1+1+1)-1 downto 0);
signal fl_async_rx0_output_pipe_in_src_rdy    : std_logic;
signal fl_async_rx0_output_pipe_in_dst_rdy    : std_logic;
signal fl_async_rx0_output_pipe_in_src_rdy_n  : std_logic;
signal fl_async_rx0_output_pipe_in_dst_rdy_n  : std_logic;
signal fl_async_rx0_output_pipe_out_data      : std_logic_vector((64+3+1+1+1+1)-1 downto 0);
signal fl_async_rx0_output_pipe_out_src_rdy   : std_logic;
signal fl_async_rx0_output_pipe_out_dst_rdy   : std_logic;
signal fl_async_rx0_output_pipe_out_src_rdy_n : std_logic;
signal fl_async_rx0_output_pipe_out_dst_rdy_n : std_logic;

signal ics_rx1_data     : std_logic_vector(63 downto 0);
signal ics_rx1_drem     : std_logic_vector(2 downto 0);
signal ics_rx1_sop_n    : std_logic;
signal ics_rx1_eop_n    : std_logic;
signal ics_rx1_sof_n    : std_logic;
signal ics_rx1_eof_n    : std_logic;
signal ics_rx1_src_rdy_n: std_logic;
signal ics_rx1_dst_rdy_n: std_logic;

signal fl_async_rx1_input_pipe_in_data       : std_logic_vector((64+3+1+1+1+1)-1 downto 0);
signal fl_async_rx1_input_pipe_in_src_rdy    : std_logic;
signal fl_async_rx1_input_pipe_in_dst_rdy    : std_logic;
signal fl_async_rx1_input_pipe_in_src_rdy_n  : std_logic;
signal fl_async_rx1_input_pipe_in_dst_rdy_n  : std_logic;
signal fl_async_rx1_input_pipe_out_data      : std_logic_vector((64+3+1+1+1+1)-1 downto 0);
signal fl_async_rx1_input_pipe_out_src_rdy   : std_logic;
signal fl_async_rx1_input_pipe_out_dst_rdy   : std_logic;
signal fl_async_rx1_input_pipe_out_src_rdy_n : std_logic;
signal fl_async_rx1_input_pipe_out_dst_rdy_n : std_logic;

signal fl_async_rx1_output_pipe_in_data       : std_logic_vector((64+3+1+1+1+1)-1 downto 0);
signal fl_async_rx1_output_pipe_in_src_rdy    : std_logic;
signal fl_async_rx1_output_pipe_in_dst_rdy    : std_logic;
signal fl_async_rx1_output_pipe_in_src_rdy_n  : std_logic;
signal fl_async_rx1_output_pipe_in_dst_rdy_n  : std_logic;
signal fl_async_rx1_output_pipe_out_data      : std_logic_vector((64+3+1+1+1+1)-1 downto 0);
signal fl_async_rx1_output_pipe_out_src_rdy   : std_logic;
signal fl_async_rx1_output_pipe_out_dst_rdy   : std_logic;
signal fl_async_rx1_output_pipe_out_src_rdy_n : std_logic;
signal fl_async_rx1_output_pipe_out_dst_rdy_n : std_logic;

signal ics_tx0_data     : std_logic_vector(63 downto 0);
signal ics_tx0_drem     : std_logic_vector(2 downto 0);
signal ics_tx0_sop_n    : std_logic;
signal ics_tx0_eop_n    : std_logic;
signal ics_tx0_sof_n    : std_logic;
signal ics_tx0_eof_n    : std_logic;
signal ics_tx0_src_rdy_n: std_logic;
signal ics_tx0_dst_rdy_n: std_logic;

signal fl_async_tx0_input_pipe_in_data       : std_logic_vector((64+3+1+1+1+1)-1 downto 0);
signal fl_async_tx0_input_pipe_in_src_rdy    : std_logic;
signal fl_async_tx0_input_pipe_in_dst_rdy    : std_logic;
signal fl_async_tx0_input_pipe_in_src_rdy_n  : std_logic;
signal fl_async_tx0_input_pipe_in_dst_rdy_n  : std_logic;
signal fl_async_tx0_input_pipe_out_data      : std_logic_vector((64+3+1+1+1+1)-1 downto 0);
signal fl_async_tx0_input_pipe_out_src_rdy   : std_logic;
signal fl_async_tx0_input_pipe_out_dst_rdy   : std_logic;
signal fl_async_tx0_input_pipe_out_src_rdy_n : std_logic;
signal fl_async_tx0_input_pipe_out_dst_rdy_n : std_logic;

signal fl_async_tx0_output_pipe_in_data       : std_logic_vector((64+3+1+1+1+1)-1 downto 0);
signal fl_async_tx0_output_pipe_in_src_rdy    : std_logic;
signal fl_async_tx0_output_pipe_in_dst_rdy    : std_logic;
signal fl_async_tx0_output_pipe_in_src_rdy_n  : std_logic;
signal fl_async_tx0_output_pipe_in_dst_rdy_n  : std_logic;
signal fl_async_tx0_output_pipe_out_data      : std_logic_vector((64+3+1+1+1+1)-1 downto 0);
signal fl_async_tx0_output_pipe_out_src_rdy   : std_logic;
signal fl_async_tx0_output_pipe_out_dst_rdy   : std_logic;
signal fl_async_tx0_output_pipe_out_src_rdy_n : std_logic;
signal fl_async_tx0_output_pipe_out_dst_rdy_n : std_logic;

signal ics_tx1_data     : std_logic_vector(63 downto 0);
signal ics_tx1_drem     : std_logic_vector(2 downto 0);
signal ics_tx1_sop_n    : std_logic;
signal ics_tx1_eop_n    : std_logic;
signal ics_tx1_sof_n    : std_logic;
signal ics_tx1_eof_n    : std_logic;
signal ics_tx1_src_rdy_n: std_logic;
signal ics_tx1_dst_rdy_n: std_logic;

signal fl_async_tx1_input_pipe_in_data       : std_logic_vector((64+3+1+1+1+1)-1 downto 0);
signal fl_async_tx1_input_pipe_in_src_rdy    : std_logic;
signal fl_async_tx1_input_pipe_in_dst_rdy    : std_logic;
signal fl_async_tx1_input_pipe_in_src_rdy_n  : std_logic;
signal fl_async_tx1_input_pipe_in_dst_rdy_n  : std_logic;
signal fl_async_tx1_input_pipe_out_data      : std_logic_vector((64+3+1+1+1+1)-1 downto 0);
signal fl_async_tx1_input_pipe_out_src_rdy   : std_logic;
signal fl_async_tx1_input_pipe_out_dst_rdy   : std_logic;
signal fl_async_tx1_input_pipe_out_src_rdy_n : std_logic;
signal fl_async_tx1_input_pipe_out_dst_rdy_n : std_logic;

signal fl_async_tx1_output_pipe_in_data       : std_logic_vector((64+3+1+1+1+1)-1 downto 0);
signal fl_async_tx1_output_pipe_in_src_rdy    : std_logic;
signal fl_async_tx1_output_pipe_in_dst_rdy    : std_logic;
signal fl_async_tx1_output_pipe_in_src_rdy_n  : std_logic;
signal fl_async_tx1_output_pipe_in_dst_rdy_n  : std_logic;
signal fl_async_tx1_output_pipe_out_data      : std_logic_vector((64+3+1+1+1+1)-1 downto 0);
signal fl_async_tx1_output_pipe_out_src_rdy   : std_logic;
signal fl_async_tx1_output_pipe_out_dst_rdy   : std_logic;
signal fl_async_tx1_output_pipe_out_src_rdy_n : std_logic;
signal fl_async_tx1_output_pipe_out_dst_rdy_n : std_logic;

begin
   RXTX_BUFFERS_I : entity work.RXTX_BUFFERS_64b
      generic map(
         -- number of network interfaces
         NET_IFC_COUNT              => 2,
         -- RX/TX Buffer generics
         BLOCK_SIZE                 => RXTX_BLOCK_SIZE,
         RXTXBUF_IFC_TOTAL_SIZE     => RXTX_IFC_TOTAL_SIZE,
         TX_SIZE_LENGTH             => RXTX_TX_SIZE_LENGTH,
         -- DMA Controller generics
         BUFFER_ADDR                => RXTX_BUFFER_ADDR,
         BUFFER_SIZE                => RXTX_BUFFER_SIZE,
         DESC_BLOCK_SIZE            => RXTX_OPT_DESC_BLOCK_SIZE,
         DESC_BASE_ADDR             => RXTX_DESC_BASE_ADDR,
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
         -- network interfaces interface
         -- input FrameLink interface
         RX_SOF_N(0)             => ics_rx0_sof_n,
         RX_SOF_N(1)             => ics_rx1_sof_n,
   
         RX_SOP_N(0)             => ics_rx0_sop_n,
         RX_SOP_N(1)             => ics_rx1_sop_n,
   
         RX_EOP_N(0)             => ics_rx0_eop_n,
         RX_EOP_N(1)             => ics_rx1_eop_n,
   
         RX_EOF_N(0)             => ics_rx0_eof_n,
         RX_EOF_N(1)             => ics_rx1_eof_n,
   
         RX_SRC_RDY_N(0)         => ics_rx0_src_rdy_n,
         RX_SRC_RDY_N(1)         => ics_rx1_src_rdy_n,
   
         RX_DST_RDY_N(0)         => ics_rx0_dst_rdy_n,
         RX_DST_RDY_N(1)         => ics_rx1_dst_rdy_n,
   
         RX_DATA( 63 downto  0)  => ics_rx0_data,
         RX_DATA(127 downto 64)  => ics_rx1_data,
   
         RX_REM(2 downto 0)      => ics_rx0_drem,
         RX_REM(5 downto 3)      => ics_rx1_drem,

         -- output FrameLink interface
         TX_SOF_N(0)             => ics_tx0_sof_n,
         TX_SOF_N(1)             => ics_tx1_sof_n,

         TX_SOP_N(0)             => ics_tx0_sop_n,
         TX_SOP_N(1)             => ics_tx1_sop_n,

         TX_EOP_N(0)             => ics_tx0_eop_n,
         TX_EOP_N(1)             => ics_tx1_eop_n,

         TX_EOF_N(0)             => ics_tx0_eof_n,
         TX_EOF_N(1)             => ics_tx1_eof_n,

         TX_SRC_RDY_N(0)         => ics_tx0_src_rdy_n,
         TX_SRC_RDY_N(1)         => ics_tx1_src_rdy_n,

         TX_DST_RDY_N(0)         => ics_tx0_dst_rdy_n,
         TX_DST_RDY_N(1)         => ics_tx1_dst_rdy_n,

         TX_DATA( 63 downto  0)  => ics_tx0_data,
         TX_DATA(127 downto 64)  => ics_tx1_data,

         TX_REM(2 downto 0)      => ics_tx0_drem,
         TX_REM(5 downto 3)      => ics_tx1_drem,
   
         -- Internal Bus interface
         IB_DOWN_DATA       => IB_DOWN_DATA,
         IB_DOWN_SOF_N      => IB_DOWN_SOF_N,
         IB_DOWN_EOF_N      => IB_DOWN_EOF_N,
         IB_DOWN_SRC_RDY_N  => IB_DOWN_SRC_RDY_N,
         IB_DOWN_DST_RDY_N  => IB_DOWN_DST_RDY_N,
         IB_UP_DATA         => IB_UP_DATA,
         IB_UP_SOF_N        => IB_UP_SOF_N,
         IB_UP_EOF_N        => IB_UP_EOF_N,
         IB_UP_SRC_RDY_N    => IB_UP_SRC_RDY_N,
         IB_UP_DST_RDY_N    => IB_UP_DST_RDY_N,
          
         -- MI32 interface
         MI32_DWR           => MI32_DWR,
         MI32_ADDR          => MI32_ADDR,
         MI32_RD            => MI32_RD,
         MI32_WR            => MI32_WR,
         MI32_BE            => MI32_BE,
         MI32_DRD           => MI32_DRD,
         MI32_ARDY          => MI32_ARDY,
         MI32_DRDY          => MI32_DRDY
      );

      -- ----------------------------------------------------------------------
      fl_async_rx0_input_pipe_in_data        <= RX0_DATA & RX0_DREM & 
                                                RX0_EOP_N & RX0_SOP_N & RX0_EOF_N & RX0_SOF_N;
      fl_async_rx0_input_pipe_in_src_rdy     <= not RX0_SRC_RDY_N;
      RX0_DST_RDY_N                          <= not fl_async_rx0_input_pipe_in_dst_rdy;

      FL_ASYNC_RX0_INPUT_PIPE : entity work.pipe
      generic map(
         DATA_WIDTH  => 64+3+1+1+1+1,
         USE_OUTREG  => true
      )
      port map(
         CLK         => USER_CLK,
         RESET       => USER_RESET,

         IN_DATA     => fl_async_rx0_input_pipe_in_data,
         IN_SRC_RDY  => fl_async_rx0_input_pipe_in_src_rdy,
         IN_DST_RDY  => fl_async_rx0_input_pipe_in_dst_rdy,
         OUT_DATA    => fl_async_rx0_input_pipe_out_data,
         OUT_SRC_RDY => fl_async_rx0_input_pipe_out_src_rdy,
         OUT_DST_RDY => fl_async_rx0_input_pipe_out_dst_rdy
      );

      fl_async_rx0_input_pipe_out_src_rdy_n  <= not fl_async_rx0_input_pipe_out_src_rdy;
      fl_async_rx0_input_pipe_out_dst_rdy   <= not fl_async_rx0_input_pipe_out_dst_rdy_n;

      -- Clock domain transfer: USER -> ICS (RX)
      FL_ASYNC_RX0 : entity work.fl_asfifo_cv2_64b
      port map(
         RX_CLK      => USER_CLK,
         RX_RESET    => USER_RESET,
         TX_CLK      => CLK,
         TX_RESET    => RESET,

         RX_DATA     => fl_async_rx0_input_pipe_out_data(70 downto 7), --RX0_DATA,
         RX_REM      => fl_async_rx0_input_pipe_out_data(6 downto 4), --RX0_DREM,
         RX_EOP_N    => fl_async_rx0_input_pipe_out_data(3), --RX0_EOP_N,
         RX_SOP_N    => fl_async_rx0_input_pipe_out_data(2), --RX0_SOP_N,
         RX_EOF_N    => fl_async_rx0_input_pipe_out_data(1), --RX0_EOF_N,
         RX_SOF_N    => fl_async_rx0_input_pipe_out_data(0), --RX0_SOF_N,
         RX_SRC_RDY_N=> fl_async_rx0_input_pipe_out_src_rdy_n, --RX0_SRC_RDY_N,
         RX_DST_RDY_N=> fl_async_rx0_input_pipe_out_dst_rdy_n, --RX0_DST_RDY_N,

         TX_DATA     => fl_async_rx0_output_pipe_in_data(70 downto 7), --ics_rx0_data,
         TX_REM      => fl_async_rx0_output_pipe_in_data(6 downto 4), --ics_rx0_drem,
         TX_EOP_N    => fl_async_rx0_output_pipe_in_data(3), --ics_rx0_eop_n,
         TX_SOP_N    => fl_async_rx0_output_pipe_in_data(2), --ics_rx0_sop_n,
         TX_EOF_N    => fl_async_rx0_output_pipe_in_data(1), --ics_rx0_eof_n,
         TX_SOF_N    => fl_async_rx0_output_pipe_in_data(0), --ics_rx0_sof_n,
         TX_SRC_RDY_N=> fl_async_rx0_output_pipe_in_src_rdy_n, --ics_rx0_src_rdy_n,
         TX_DST_RDY_N=> fl_async_rx0_output_pipe_in_dst_rdy_n --ics_rx0_dst_rdy_n
      );

      fl_async_rx0_output_pipe_in_src_rdy    <= not fl_async_rx0_output_pipe_in_src_rdy_n;
      fl_async_rx0_output_pipe_in_dst_rdy_n  <= not fl_async_rx0_output_pipe_in_dst_rdy;

      FL_ASYNC_RX0_OUTPUT_PIPE : entity work.pipe
      generic map(
         DATA_WIDTH  => 64+3+1+1+1+1,
         USE_OUTREG  => true
      )
      port map(
         CLK         => CLK,
         RESET       => RESET,

         IN_DATA     => fl_async_rx0_output_pipe_in_data,
         IN_SRC_RDY  => fl_async_rx0_output_pipe_in_src_rdy,
         IN_DST_RDY  => fl_async_rx0_output_pipe_in_dst_rdy,
         OUT_DATA    => fl_async_rx0_output_pipe_out_data,
         OUT_SRC_RDY => fl_async_rx0_output_pipe_out_src_rdy,
         OUT_DST_RDY => fl_async_rx0_output_pipe_out_dst_rdy
      );
    
      ics_rx0_data   <= fl_async_rx0_output_pipe_out_data(70 downto 7);
      ics_rx0_drem   <= fl_async_rx0_output_pipe_out_data(6 downto 4);
      ics_rx0_eop_n  <= fl_async_rx0_output_pipe_out_data(3); 
      ics_rx0_sop_n  <= fl_async_rx0_output_pipe_out_data(2); 
      ics_rx0_eof_n  <= fl_async_rx0_output_pipe_out_data(1);                                 
      ics_rx0_sof_n  <= fl_async_rx0_output_pipe_out_data(0);

      ics_rx0_src_rdy_n                      <= not fl_async_rx0_output_pipe_out_src_rdy;
      fl_async_rx0_output_pipe_out_dst_rdy   <= not ics_rx0_dst_rdy_n;

      -- --------------------------------------------------------------------
      fl_async_rx1_input_pipe_in_data        <= RX1_DATA & RX1_DREM & 
                                                RX1_EOP_N & RX1_SOP_N & RX1_EOF_N & RX1_SOF_N;
      fl_async_rx1_input_pipe_in_src_rdy     <= not RX1_SRC_RDY_N;
      RX1_DST_RDY_N                          <= not fl_async_rx1_input_pipe_in_dst_rdy;

      FL_ASYNC_RX1_INPUT_PIPE : entity work.pipe
      generic map(
         DATA_WIDTH  => 64+3+1+1+1+1,
         USE_OUTREG  => true
      )
      port map(
         CLK         => USER_CLK,
         RESET       => USER_RESET,

         IN_DATA     => fl_async_rx1_input_pipe_in_data,
         IN_SRC_RDY  => fl_async_rx1_input_pipe_in_src_rdy,
         IN_DST_RDY  => fl_async_rx1_input_pipe_in_dst_rdy,
         OUT_DATA    => fl_async_rx1_input_pipe_out_data,
         OUT_SRC_RDY => fl_async_rx1_input_pipe_out_src_rdy,
         OUT_DST_RDY => fl_async_rx1_input_pipe_out_dst_rdy
      );

      fl_async_rx1_input_pipe_out_src_rdy_n  <= not fl_async_rx1_input_pipe_out_src_rdy;
      fl_async_rx1_input_pipe_out_dst_rdy   <= not fl_async_rx1_input_pipe_out_dst_rdy_n;

      -- Clock domain transfer: USER -> ICS (RX)
      FL_ASYNC_RX1 : entity work.fl_asfifo_cv2_64b
      port map(
         RX_CLK      => USER_CLK,
         RX_RESET    => USER_RESET,
         TX_CLK      => CLK,
         TX_RESET    => RESET,

         RX_DATA     => fl_async_rx1_input_pipe_out_data(70 downto 7), --RX1_DATA,
         RX_REM      => fl_async_rx1_input_pipe_out_data(6 downto 4), --RX1_DREM,
         RX_EOP_N    => fl_async_rx1_input_pipe_out_data(3), --RX1_EOP_N,
         RX_SOP_N    => fl_async_rx1_input_pipe_out_data(2), --RX1_SOP_N,
         RX_EOF_N    => fl_async_rx1_input_pipe_out_data(1), --RX1_EOF_N,
         RX_SOF_N    => fl_async_rx1_input_pipe_out_data(0), --RX1_SOF_N,
         RX_SRC_RDY_N=> fl_async_rx1_input_pipe_out_src_rdy_n, --RX1_SRC_RDY_N,
         RX_DST_RDY_N=> fl_async_rx1_input_pipe_out_dst_rdy_n, --RX1_DST_RDY_N,

         TX_DATA     => fl_async_rx1_output_pipe_in_data(70 downto 7), --ics_rx1_data,
         TX_REM      => fl_async_rx1_output_pipe_in_data(6 downto 4), --ics_rx1_drem,
         TX_EOP_N    => fl_async_rx1_output_pipe_in_data(3), --ics_rx1_eop_n,
         TX_SOP_N    => fl_async_rx1_output_pipe_in_data(2), --ics_rx1_sop_n,
         TX_EOF_N    => fl_async_rx1_output_pipe_in_data(1), --ics_rx1_eof_n,
         TX_SOF_N    => fl_async_rx1_output_pipe_in_data(0), --ics_rx1_sof_n,
         TX_SRC_RDY_N=> fl_async_rx1_output_pipe_in_src_rdy_n, --ics_rx1_src_rdy_n,
         TX_DST_RDY_N=> fl_async_rx1_output_pipe_in_dst_rdy_n --ics_rx1_dst_rdy_n
      );

      fl_async_rx1_output_pipe_in_src_rdy    <= not fl_async_rx1_output_pipe_in_src_rdy_n;
      fl_async_rx1_output_pipe_in_dst_rdy_n  <= not fl_async_rx1_output_pipe_in_dst_rdy;

      FL_ASYNC_RX1_OUTPUT_PIPE : entity work.pipe
      generic map(
         DATA_WIDTH  => 64+3+1+1+1+1,
         USE_OUTREG  => true
      )
      port map(
         CLK         => CLK,
         RESET       => RESET,

         IN_DATA     => fl_async_rx1_output_pipe_in_data,
         IN_SRC_RDY  => fl_async_rx1_output_pipe_in_src_rdy,
         IN_DST_RDY  => fl_async_rx1_output_pipe_in_dst_rdy,
         OUT_DATA    => fl_async_rx1_output_pipe_out_data,
         OUT_SRC_RDY => fl_async_rx1_output_pipe_out_src_rdy,
         OUT_DST_RDY => fl_async_rx1_output_pipe_out_dst_rdy
      );
    
      ics_rx1_data   <= fl_async_rx1_output_pipe_out_data(70 downto 7);
      ics_rx1_drem   <= fl_async_rx1_output_pipe_out_data(6 downto 4);
      ics_rx1_eop_n  <= fl_async_rx1_output_pipe_out_data(3); 
      ics_rx1_sop_n  <= fl_async_rx1_output_pipe_out_data(2); 
      ics_rx1_eof_n  <= fl_async_rx1_output_pipe_out_data(1);                                 
      ics_rx1_sof_n  <= fl_async_rx1_output_pipe_out_data(0);

      ics_rx1_src_rdy_n                      <= not fl_async_rx1_output_pipe_out_src_rdy;
      fl_async_rx1_output_pipe_out_dst_rdy   <= not ics_rx1_dst_rdy_n;
      -- ----------------------------------------------------------------------

      fl_async_tx0_input_pipe_in_data        <= ics_tx0_data & ics_tx0_drem & 
                                                ics_tx0_eop_n & ics_tx0_sop_n & ics_tx0_eof_n & ics_tx0_sof_n;
      fl_async_tx0_input_pipe_in_src_rdy     <= not ics_tx0_src_rdy_n;
      ics_tx0_dst_rdy_n                      <= not fl_async_tx0_input_pipe_in_dst_rdy;

      FL_ASYNC_TX0_INPUT_PIPE : entity work.pipe
      generic map(
         DATA_WIDTH  => 64+3+1+1+1+1,
         USE_OUTREG  => true
      )
      port map(
         CLK         => CLK,
         RESET       => RESET,

         IN_DATA     => fl_async_tx0_input_pipe_in_data,
         IN_SRC_RDY  => fl_async_tx0_input_pipe_in_src_rdy,
         IN_DST_RDY  => fl_async_tx0_input_pipe_in_dst_rdy,
         OUT_DATA    => fl_async_tx0_input_pipe_out_data,
         OUT_SRC_RDY => fl_async_tx0_input_pipe_out_src_rdy,
         OUT_DST_RDY => fl_async_tx0_input_pipe_out_dst_rdy
      );

      fl_async_tx0_input_pipe_out_src_rdy_n  <= not fl_async_tx0_input_pipe_out_src_rdy;
      fl_async_tx0_input_pipe_out_dst_rdy   <= not fl_async_tx0_input_pipe_out_dst_rdy_n;

      -- Clock domain transfer ICS -> USER (TX)
      FL_ASYNC_TX0 : entity work.fl_asfifo_cv2_64b
      port map(
         RX_CLK      => CLK,
         RX_RESET    => RESET,
         TX_CLK      => USER_CLK,
         TX_RESET    => USER_RESET,

         RX_DATA     => fl_async_tx0_input_pipe_out_data(70 downto 7), --ics_tx0_data,
         RX_REM      => fl_async_tx0_input_pipe_out_data(6 downto 4), --ics_tx0_drem,
         RX_EOP_N    => fl_async_tx0_input_pipe_out_data(3), --ics_tx0_eop_n,
         RX_SOP_N    => fl_async_tx0_input_pipe_out_data(2), --ics_tx0_sop_n,
         RX_EOF_N    => fl_async_tx0_input_pipe_out_data(1), --ics_tx0_eof_n,
         RX_SOF_N    => fl_async_tx0_input_pipe_out_data(0), --ics_tx0_sof_n,
         RX_SRC_RDY_N=> fl_async_tx0_input_pipe_out_src_rdy_n, --ics_tx0_src_rdy_n,
         RX_DST_RDY_N=> fl_async_tx0_input_pipe_out_dst_rdy_n, --ics_tx0_dst_rdy_n,

         TX_DATA     => fl_async_tx0_output_pipe_in_data(70 downto 7), --TX0_DATA,
         TX_REM      => fl_async_tx0_output_pipe_in_data(6 downto 4), --TX0_DREM,
         TX_EOP_N    => fl_async_tx0_output_pipe_in_data(3), --TX0_EOP_N,
         TX_SOP_N    => fl_async_tx0_output_pipe_in_data(2), --TX0_SOP_N,
         TX_EOF_N    => fl_async_tx0_output_pipe_in_data(1), --TX0_EOF_N,
         TX_SOF_N    => fl_async_tx0_output_pipe_in_data(0), --TX0_SOF_N,
         TX_SRC_RDY_N=> fl_async_tx0_output_pipe_in_src_rdy_n, --TX0_SRC_RDY_N,
         TX_DST_RDY_N=> fl_async_tx0_output_pipe_in_dst_rdy_n --TX0_DST_RDY_N
      );

      fl_async_tx0_output_pipe_in_src_rdy    <= not fl_async_tx0_output_pipe_in_src_rdy_n;
      fl_async_tx0_output_pipe_in_dst_rdy_n  <= not fl_async_tx0_output_pipe_in_dst_rdy;

      FL_ASYNC_TX0_OUTPUT_PIPE : entity work.pipe
      generic map(
         DATA_WIDTH  => 64+3+1+1+1+1,
         USE_OUTREG  => true
      )
      port map(
         CLK         => USER_CLK,
         RESET       => USER_RESET,

         IN_DATA     => fl_async_tx0_output_pipe_in_data,
         IN_SRC_RDY  => fl_async_tx0_output_pipe_in_src_rdy,
         IN_DST_RDY  => fl_async_tx0_output_pipe_in_dst_rdy,
         OUT_DATA    => fl_async_tx0_output_pipe_out_data,
         OUT_SRC_RDY => fl_async_tx0_output_pipe_out_src_rdy,
         OUT_DST_RDY => fl_async_tx0_output_pipe_out_dst_rdy
      );
    
      TX0_DATA   <= fl_async_tx0_output_pipe_out_data(70 downto 7);
      TX0_DREM   <= fl_async_tx0_output_pipe_out_data(6 downto 4);
      TX0_EOP_N  <= fl_async_tx0_output_pipe_out_data(3); 
      TX0_SOP_N  <= fl_async_tx0_output_pipe_out_data(2); 
      TX0_EOF_N  <= fl_async_tx0_output_pipe_out_data(1);                                 
      TX0_SOF_N  <= fl_async_tx0_output_pipe_out_data(0);

      TX0_SRC_RDY_N                          <= not fl_async_tx0_output_pipe_out_src_rdy;
      fl_async_tx0_output_pipe_out_dst_rdy   <= not TX0_dst_rdy_n;
      -- ----------------------------------------------------------------------

      fl_async_tx1_input_pipe_in_data        <= ics_tx1_data & ics_tx1_drem & 
                                                ics_tx1_eop_n & ics_tx1_sop_n & ics_tx1_eof_n & ics_tx1_sof_n;
      fl_async_tx1_input_pipe_in_src_rdy     <= not ics_tx1_src_rdy_n;
      ics_tx1_dst_rdy_n                      <= not fl_async_tx1_input_pipe_in_dst_rdy;

      FL_ASYNC_TX1_INPUT_PIPE : entity work.pipe
      generic map(
         DATA_WIDTH  => 64+3+1+1+1+1,
         USE_OUTREG  => true
      )
      port map(
         CLK         => CLK,
         RESET       => RESET,

         IN_DATA     => fl_async_tx1_input_pipe_in_data,
         IN_SRC_RDY  => fl_async_tx1_input_pipe_in_src_rdy,
         IN_DST_RDY  => fl_async_tx1_input_pipe_in_dst_rdy,
         OUT_DATA    => fl_async_tx1_input_pipe_out_data,
         OUT_SRC_RDY => fl_async_tx1_input_pipe_out_src_rdy,
         OUT_DST_RDY => fl_async_tx1_input_pipe_out_dst_rdy
      );

      fl_async_tx1_input_pipe_out_src_rdy_n  <= not fl_async_tx1_input_pipe_out_src_rdy;
      fl_async_tx1_input_pipe_out_dst_rdy   <= not fl_async_tx1_input_pipe_out_dst_rdy_n;

      -- Clock domain transfer ICS -> USER (TX)
      FL_ASYNC_TX1 : entity work.fl_asfifo_cv2_64b
      port map(
         RX_CLK      => CLK,
         RX_RESET    => RESET,
         TX_CLK      => USER_CLK,
         TX_RESET    => USER_RESET,

         RX_DATA     => fl_async_tx1_input_pipe_out_data(70 downto 7), --ics_tx1_data,
         RX_REM      => fl_async_tx1_input_pipe_out_data(6 downto 4), --ics_tx1_drem,
         RX_EOP_N    => fl_async_tx1_input_pipe_out_data(3), --ics_tx1_eop_n,
         RX_SOP_N    => fl_async_tx1_input_pipe_out_data(2), --ics_tx1_sop_n,
         RX_EOF_N    => fl_async_tx1_input_pipe_out_data(1), --ics_tx1_eof_n,
         RX_SOF_N    => fl_async_tx1_input_pipe_out_data(0), --ics_tx1_sof_n,
         RX_SRC_RDY_N=> fl_async_tx1_input_pipe_out_src_rdy_n, --ics_tx1_src_rdy_n,
         RX_DST_RDY_N=> fl_async_tx1_input_pipe_out_dst_rdy_n, --ics_tx1_dst_rdy_n,

         TX_DATA     => fl_async_tx1_output_pipe_in_data(70 downto 7), --TX1_DATA,
         TX_REM      => fl_async_tx1_output_pipe_in_data(6 downto 4), --TX1_DREM,
         TX_EOP_N    => fl_async_tx1_output_pipe_in_data(3), --TX1_EOP_N,
         TX_SOP_N    => fl_async_tx1_output_pipe_in_data(2), --TX1_SOP_N,
         TX_EOF_N    => fl_async_tx1_output_pipe_in_data(1), --TX1_EOF_N,
         TX_SOF_N    => fl_async_tx1_output_pipe_in_data(0), --TX1_SOF_N,
         TX_SRC_RDY_N=> fl_async_tx1_output_pipe_in_src_rdy_n, --TX1_SRC_RDY_N,
         TX_DST_RDY_N=> fl_async_tx1_output_pipe_in_dst_rdy_n --TX1_DST_RDY_N
      );

      fl_async_tx1_output_pipe_in_src_rdy    <= not fl_async_tx1_output_pipe_in_src_rdy_n;
      fl_async_tx1_output_pipe_in_dst_rdy_n  <= not fl_async_tx1_output_pipe_in_dst_rdy;

      FL_ASYNC_TX1_OUTPUT_PIPE : entity work.pipe
      generic map(
         DATA_WIDTH  => 64+3+1+1+1+1,
         USE_OUTREG  => true
      )
      port map(
         CLK         => USER_CLK,
         RESET       => USER_RESET,

         IN_DATA     => fl_async_tx1_output_pipe_in_data,
         IN_SRC_RDY  => fl_async_tx1_output_pipe_in_src_rdy,
         IN_DST_RDY  => fl_async_tx1_output_pipe_in_dst_rdy,
         OUT_DATA    => fl_async_tx1_output_pipe_out_data,
         OUT_SRC_RDY => fl_async_tx1_output_pipe_out_src_rdy,
         OUT_DST_RDY => fl_async_tx1_output_pipe_out_dst_rdy
      );
    
      TX1_DATA   <= fl_async_tx1_output_pipe_out_data(70 downto 7);
      TX1_DREM   <= fl_async_tx1_output_pipe_out_data(6 downto 4);
      TX1_EOP_N  <= fl_async_tx1_output_pipe_out_data(3); 
      TX1_SOP_N  <= fl_async_tx1_output_pipe_out_data(2); 
      TX1_EOF_N  <= fl_async_tx1_output_pipe_out_data(1);                                 
      TX1_SOF_N  <= fl_async_tx1_output_pipe_out_data(0);

      TX1_SRC_RDY_N                          <= not fl_async_tx1_output_pipe_out_src_rdy;
      fl_async_tx1_output_pipe_out_dst_rdy   <= not TX1_dst_rdy_n;

end architecture;
-- ----------------------------------------------------------------------------
