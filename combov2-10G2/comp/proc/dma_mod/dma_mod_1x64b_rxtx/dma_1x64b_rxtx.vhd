-- dma_1x64b_rxtx.vhd: DMA Module for 1x64 RX+TX interface
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

use work.dma_mod_1x64b_rxtx_const.all;

entity DMA_MOD_1x64b_RXTX is
   port(
      -- Common interface
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- USER Clock and RESET - driver FL_ASFIFOs and FL ifcs
      USER_CLK       : in  std_logic;
      USER_RESET     : in  std_logic;

      RX_INTERRUPT   : out std_logic;
      TX_INTERRUPT   : out std_logic;
      
      -- network interfaces interface
      -- input interface
      RX0_DATA       : in  std_logic_vector(63 downto 0);
      RX0_DREM       : in  std_logic_vector(2 downto 0);
      RX0_SOF_N      : in  std_logic;
      RX0_EOF_N      : in  std_logic;
      RX0_SOP_N      : in  std_logic;
      RX0_EOP_N      : in  std_logic;
      RX0_SRC_RDY_N  : in  std_logic;
      RX0_DST_RDY_N  : out std_logic;

      -- output interfaces
      TX0_DATA       : out std_logic_vector(63 downto 0);
      TX0_DREM       : out std_logic_vector(2 downto 0);
      TX0_SOF_N      : out std_logic;
      TX0_EOF_N      : out std_logic;
      TX0_SOP_N      : out std_logic;
      TX0_EOP_N      : out std_logic;
      TX0_SRC_RDY_N  : out std_logic;
      TX0_DST_RDY_N  : in  std_logic;

      -- Internal Bus - CLK (ICS Clock)
      IB_DOWN_DATA      : in  std_logic_vector(63 downto 0);
      IB_DOWN_SOF_N     : in  std_logic;
      IB_DOWN_EOF_N     : in  std_logic;
      IB_DOWN_SRC_RDY_N : in  std_logic;
      IB_DOWN_DST_RDY_N : out std_logic;
      IB_UP_DATA        : out std_logic_vector(63 downto 0);
      IB_UP_SOF_N       : out std_logic;
      IB_UP_EOF_N       : out std_logic;
      IB_UP_SRC_RDY_N   : out std_logic;
      IB_UP_DST_RDY_N   : in  std_logic;

      -- MI32 interface - CLK (ICS Clock)
      MI32_DWR          : in  std_logic_vector(31 downto 0);
      MI32_ADDR         : in  std_logic_vector(31 downto 0);
      MI32_RD           : in  std_logic;
      MI32_WR           : in  std_logic;
      MI32_BE           : in  std_logic_vector(3 downto 0);
      MI32_DRD          : out std_logic_vector(31 downto 0);
      MI32_ARDY         : out std_logic;
      MI32_DRDY         : out std_logic
   );
end entity DMA_MOD_1x64b_RXTX;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of DMA_MOD_1x64b_RXTX is
   signal ics_rx0_data     : std_logic_vector(63 downto 0);
   signal ics_rx0_drem     : std_logic_vector(2 downto 0);
   signal ics_rx0_sop_n    : std_logic;
   signal ics_rx0_eop_n    : std_logic;
   signal ics_rx0_sof_n    : std_logic;
   signal ics_rx0_eof_n    : std_logic;
   signal ics_rx0_src_rdy_n: std_logic;
   signal ics_rx0_dst_rdy_n: std_logic;

   signal ics_tx0_data     : std_logic_vector(63 downto 0);
   signal ics_tx0_drem     : std_logic_vector(2 downto 0);
   signal ics_tx0_sop_n    : std_logic;
   signal ics_tx0_eop_n    : std_logic;
   signal ics_tx0_sof_n    : std_logic;
   signal ics_tx0_eof_n    : std_logic;
   signal ics_tx0_src_rdy_n: std_logic;
   signal ics_tx0_dst_rdy_n: std_logic;


begin
   RXTX_BUFFERS_I : entity work.RXTX_BUFFERS_OPT
      generic map(
         -- number of network interfaces
         NET_IFC_COUNT              => 1,
         -- RX/TX Buffer generics
         DATA_WIDTH                 => 64,
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
         RX_SOP_N(0)             => ics_rx0_sop_n,
         RX_EOP_N(0)             => ics_rx0_eop_n,
         RX_EOF_N(0)             => ics_rx0_eof_n,
         RX_SRC_RDY_N(0)         => ics_rx0_src_rdy_n,
         RX_DST_RDY_N(0)         => ics_rx0_dst_rdy_n,
         RX_DATA( 63 downto  0)  => ics_rx0_data,
         RX_REM(2 downto 0)      => ics_rx0_drem,
         -- output FrameLink interface
         TX_SOF_N(0)             => ics_tx0_sof_n,
         TX_SOP_N(0)             => ics_tx0_sop_n,
         TX_EOP_N(0)             => ics_tx0_eop_n,
         TX_EOF_N(0)             => ics_tx0_eof_n,
         TX_SRC_RDY_N(0)         => ics_tx0_src_rdy_n,
         TX_DST_RDY_N(0)         => ics_tx0_dst_rdy_n,
         TX_DATA( 63 downto  0)  => ics_tx0_data,
         TX_REM(2 downto 0)      => ics_tx0_drem,
         
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

      -- Clock domain transfer: USER -> ICS (RX)
      FL_ASYNC_RX0 : entity work.fl_asfifo_cv2_64b
      port map(
         RX_CLK      => USER_CLK,
         RX_RESET    => USER_RESET,
         TX_CLK      => CLK,
         TX_RESET    => RESET,

         RX_DATA     => rx0_DATA,
         RX_REM      => rx0_DREM,
         RX_EOP_N    => rx0_EOP_N,
         RX_SOP_N    => rx0_SOP_N,
         RX_EOF_N    => rx0_EOF_N,
         RX_SOF_N    => rx0_SOF_N,
         RX_SRC_RDY_N=> rx0_SRC_RDY_N,
         RX_DST_RDY_N=> rx0_DST_RDY_N,

         TX_DATA     => ics_rx0_data,
         TX_REM      => ics_rx0_drem,
         TX_EOP_N    => ics_rx0_eop_n,
         TX_SOP_N    => ics_rx0_sop_n,
         TX_EOF_N    => ics_rx0_eof_n,
         TX_SOF_N    => ics_rx0_sof_n,
         TX_SRC_RDY_N=> ics_rx0_src_rdy_n,
         TX_DST_RDY_N=> ics_rx0_dst_rdy_n
      );

      -- Clock domain transfer ICS -> USER (TX)
      FL_ASYNC_TX0 : entity work.fl_asfifo_cv2_64b
      port map(
         RX_CLK      => CLK,
         RX_RESET    => RESET,
         TX_CLK      => USER_CLK,
         TX_RESET    => USER_RESET,

         RX_DATA     => ics_tx0_data,
         RX_REM      => ics_tx0_drem,
         RX_EOP_N    => ics_tx0_eop_n,
         RX_SOP_N    => ics_tx0_sop_n,
         RX_EOF_N    => ics_tx0_eof_n,
         RX_SOF_N    => ics_tx0_sof_n,
         RX_SRC_RDY_N=> ics_tx0_src_rdy_n,
         RX_DST_RDY_N=> ics_tx0_dst_rdy_n,

         TX_DATA     => TX0_DATA,
         TX_REM      => TX0_DREM,
         TX_EOP_N    => TX0_EOP_N,
         TX_SOP_N    => TX0_SOP_N,
         TX_EOF_N    => TX0_EOF_N,
         TX_SOF_N    => TX0_SOF_N,
         TX_SRC_RDY_N=> TX0_SRC_RDY_N,
         TX_DST_RDY_N=> TX0_DST_RDY_N
      );

end architecture;
-- ----------------------------------------------------------------------------
