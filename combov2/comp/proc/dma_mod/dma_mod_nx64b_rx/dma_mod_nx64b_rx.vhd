-- dma_2x64b_rx_ent.vhd: DMA Module for 2x64 RX interface
-- Copyright (C) 2009 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--            Jan Vozenilek <xvozen00@stud.fit.vutbr.cz>
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

use work.dma_mod_nx64b_rx_const.all;

entity DMA_MOD_Nx64b_RX is
   generic (
      -- number of interfaces
      IFCS           : integer := 8
   );
   port(
      -- ICS Clock and RESET - drives almost whole module, also IB and LB ifcs
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- USER Clock and RESET - driver FL_ASFIFOs and FL ifcs
      USER_CLK       : in  std_logic;
      USER_RESET     : in  std_logic;

      -- Synchronous at CLK (ICS Clock)
      RX_INTERRUPT   : out std_logic;
      
      -- network interfaces - USER_CLK
      -- input interface
      RX_DATA       : in  std_logic_vector(IFCS*64-1 downto 0);
      RX_DREM       : in  std_logic_vector(IFCS*3-1 downto 0);
      RX_SOF_N      : in  std_logic_vector(IFCS-1 downto 0);
      RX_EOF_N      : in  std_logic_vector(IFCS-1 downto 0);
      RX_SOP_N      : in  std_logic_vector(IFCS-1 downto 0);
      RX_EOP_N      : in  std_logic_vector(IFCS-1 downto 0);
      RX_SRC_RDY_N  : in  std_logic_vector(IFCS-1 downto 0);
      RX_DST_RDY_N  : out std_logic_vector(IFCS-1 downto 0);

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
end entity DMA_MOD_Nx64b_RX;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of DMA_MOD_Nx64b_RX is

signal ics_rx_data     : std_logic_vector(IFCS*64-1 downto 0);
signal ics_rx_drem     : std_logic_vector(IFCS*3-1 downto 0);
signal ics_rx_sop_n    : std_logic_vector(IFCS-1 downto 0);
signal ics_rx_eop_n    : std_logic_vector(IFCS-1 downto 0);
signal ics_rx_sof_n    : std_logic_vector(IFCS-1 downto 0);
signal ics_rx_eof_n    : std_logic_vector(IFCS-1 downto 0);
signal ics_rx_src_rdy_n: std_logic_vector(IFCS-1 downto 0);
signal ics_rx_dst_rdy_n: std_logic_vector(IFCS-1 downto 0);

begin
   RX_BUFFERS_I : entity work.RX_BUFFERS_Nx64b
      generic map(
         -- number of network interfaces
         NET_IFC_COUNT              => IFCS,
         -- RX/TX Buffer generics
         BLOCK_SIZE                 => RXTX_BLOCK_SIZE,
         RXBUF_IFC_TOTAL_SIZE       => RXTX_IFC_TOTAL_SIZE,
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
         -- network interfaces interface
         -- input FrameLink interface
         RX_SOF_N       => ics_rx_sof_n,
         RX_SOP_N       => ics_rx_sop_n,
         RX_EOP_N       => ics_rx_eop_n,
         RX_EOF_N       => ics_rx_eof_n,
         RX_SRC_RDY_N   => ics_rx_src_rdy_n,
         RX_DST_RDY_N   => ics_rx_dst_rdy_n,
         RX_DATA        => ics_rx_data,
         RX_REM         => ics_rx_drem,

         --- Internal Bus interface
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

      gen_async_fifo: for i in 0 to IFCS-1 generate
      -- Clock domain transfer: USER -> ICS (RX)
         FL_ASYNC_RX_I : entity work.fl_asfifo_cv2_64b
         port map(
            RX_CLK      => USER_CLK,
            RX_RESET    => USER_RESET,
            TX_CLK      => CLK,
            TX_RESET    => RESET,

            RX_DATA     => RX_DATA((i+1)*64-1 downto i*64),
            RX_REM      => RX_DREM((i+1)*3-1 downto i*3),
            RX_EOP_N    => RX_EOP_N(i),
            RX_SOP_N    => RX_SOP_N(i),
            RX_EOF_N    => RX_EOF_N(i),
            RX_SOF_N    => RX_SOF_N(i),
            RX_SRC_RDY_N=> RX_SRC_RDY_N(i),
            RX_DST_RDY_N=> RX_DST_RDY_N(i),

            TX_DATA     => ics_rx_data((i+1)*64-1 downto i*64),
            TX_REM      => ics_rx_drem((i+1)*3-1 downto i*3),
            TX_EOP_N    => ics_rx_eop_n(i),
            TX_SOP_N    => ics_rx_sop_n(i),
            TX_EOF_N    => ics_rx_eof_n(i),
            TX_SOF_N    => ics_rx_sof_n(i),
            TX_SRC_RDY_N=> ics_rx_src_rdy_n(i),
            TX_DST_RDY_N=> ics_rx_dst_rdy_n(i)
         );

      end generate;

end architecture;
-- ----------------------------------------------------------------------------
