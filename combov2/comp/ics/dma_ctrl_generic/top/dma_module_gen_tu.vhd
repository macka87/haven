-- dma_module_gen_tu.vhd: ...
-- Copyright (C) 2010 CESNET
-- Author(s): Karel Koranda <xkoran01@stud.fit.vutbr.cz>
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
-- TODO:
--
--

--
-- místo LB MI32!!!!
--
--
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;
-- ------------------------------------------------------------
--                    Entity declaration
-- ------------------------------------------------------------
entity DMA_MODULE_GEN_TU is
   generic (
      -- number of network interfaces
      DMA_IFC_COUNT              : integer := 2;
      
      DATA_WIDTH                 : integer := 32;
      BUFFER_ADDR                : std_logic_vector(31 downto 0) := X"02000000";
      BUFFER_SIZE                : integer := 4096;
      TX_SIZE_LENGTH             : integer := 16;
      RXTXBUF_IFC_TOTAL_SIZE     : integer := 16385;
      BLOCK_SIZE                 : integer := 512;
      
      --
      --RX_IFC_COUNT               : integer := 2;
      --TX_IFC_COUNT               : integer := 2;
      
      -- RX/TX SW Buffers
      -- Data width
      --RX_DATA_WIDTH              : integer := 64;
      --TX_DATA_WIDTH              : integer := 64;
      -- Buffers block size
      --BLOCK_SIZE                 : integer := 512;
      -- Total size (in bytes) reserved in TX buffers for one interface
      --TXBUF_IFC_TOTAL_SIZE       : integer := 16384;
      -- length of one size (head or data) in used protocol (16 bits for FrameLink)
      --TX_SIZE_LENGTH             : integer := 16;
      
      -- Descriptor manager generics
      DESC_BASE_ADDR             : std_logic_vector(31 downto 0) := X"02200000";
      DESC_BLOCK_SIZE            : integer   := 4;
      
      -- Internal Bus endpoint generics
      IB_EP_LIMIT                : std_logic_vector(31 downto 0) := X"01000000";
      IB_EP_INPUT_BUFFER_SIZE    : integer := 0;
      IB_EP_OUTPUT_BUFFER_SIZE   : integer := 0;
      IB_EP_READ_REORDER_BUFFER  : boolean := true;
      IB_EP_STRICT_EN            : boolean := false; -- Enable Strict version
      
      LB_EP_BASE_ADDR            : std_logic_vector(31 downto 0) := X"00000800";
      LB_EP_LIMIT                : std_logic_vector(31 downto 0) := X"00000800";
      LB_EP_FREQUENCY            : integer := 100;
      LB_EP_BUFFER_EN            : boolean := false
      
   );
   port (
      -- Common interface
      CLK            : in std_logic;
      RESET          : in std_logic;
      -- RX/TX Interrupts
      RX_INTERRUPT   : out std_logic;
      TX_INTERRUPT   : out std_logic;
      
      -- network interfaces interface
      -- input FrameLink interface
      RX_SOF_N       : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      RX_SOP_N       : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      RX_EOF_N       : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      RX_EOP_N       : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      RX_SRC_RDY_N   : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      RX_DST_RDY_N   : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      RX_DATA        : in  std_logic_vector(DMA_IFC_COUNT*64-1 downto 0);
      RX_REM         : in  std_logic_vector(DMA_IFC_COUNT*log2(64/8)-1 downto 0);
      --RX_ADDR        : in  std_logic_vector(abs(log2(DMA_IFC_COUNT)-1) downto 0);
      -- output FrameLinks
      TX_SOF_N       : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      TX_SOP_N       : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      TX_EOF_N       : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      TX_EOP_N       : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      TX_SRC_RDY_N   : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      TX_DST_RDY_N   : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      TX_DATA        : out std_logic_vector(DMA_IFC_COUNT*64-1 downto 0);
      TX_REM         : out std_logic_vector(DMA_IFC_COUNT*log2(64/8)-1 downto 0);
      
      -- Upstream Internal Bus interface
      UP_DATA        : out std_logic_vector(63 downto 0);
      UP_SOP_N       : out std_logic;
      UP_EOP_N       : out std_logic;
      UP_SRC_RDY_N   : out std_logic;
      UP_DST_RDY_N   : in  std_logic;
      
      -- Downstream Internal Bus interface
      DOWN_DATA      : in  std_logic_vector(63 downto 0);
      DOWN_SOP_N     : in  std_logic;
      DOWN_EOP_N     : in  std_logic;
      DOWN_SRC_RDY_N : in  std_logic;
      DOWN_DST_RDY_N : out std_logic;
      
      -- LocalBus
      LB_DWR         : in std_logic_vector(15 downto 0);
      LB_BE          : in std_logic_vector(1 downto 0);
      LB_ADS_N       : in std_logic;
      LB_RD_N        : in std_logic;
      LB_WR_N        : in std_logic;
      LB_DRD         : out std_logic_vector(15 downto 0);
      LB_RDY_N       : out std_logic;
      LB_ERR_N       : out std_logic;
      LB_ABORT_N     : in std_logic
   );
end entity DMA_MODULE_GEN_TU;
-- ---------------------------------------------------------------
--                    Architecture declaration
-- ---------------------------------------------------------------
architecture behavioral of DMA_MODULE_GEN_TU is

   signal rx_mod_sof_n        : std_logic;
   signal rx_mod_sop_n        : std_logic;
   signal rx_mod_eof_n        : std_logic;
   signal rx_mod_eop_n        : std_logic;
   signal rx_mod_src_rdy_n    : std_logic;
   signal rx_mod_dst_rdy_n    : std_logic_vector(DMA_IFC_COUNT-1 downto 0);
   signal rx_mod_data         : std_logic_vector(63 downto 0);
   signal rx_mod_rem          : std_logic_vector(log2(64/8)-1 downto 0);
   signal rx_mod_addr         : std_logic_vector(abs(log2(DMA_IFC_COUNT)-1) downto 0);

   -- MI32 interface signals
   signal mi32_dwr            : std_logic_vector(31 downto 0);
   signal mi32_be             : std_logic_vector(3 downto 0);
   signal mi32_addr           : std_logic_vector(31 downto 0);
   signal mi32_drd            : std_logic_vector(31 downto 0);
   signal mi32_ardy           : std_logic;
   signal mi32_drdy           : std_logic;
   signal mi32_rd             : std_logic;
   signal mi32_wr             : std_logic;

begin

   DMA_MODULE_GEN_I : entity work.DMA_MODULE_GEN
      generic map (
         -- number of network interfaces
         RX_IFC_COUNT               => DMA_IFC_COUNT,
         TX_IFC_COUNT               => DMA_IFC_COUNT,
         
         -- RX/TX SW Buffers
         -- Data width
         --DATA_WIDTH                 => DATA_WIDTH,
         -- Buffers block size
         BLOCK_SIZE                 => BLOCK_SIZE,
         
         RX_DISCARD_EN              => false,
      
         -- Descriptor manager generics
         DESC_BASE_ADDR             => DESC_BASE_ADDR,
         DESC_BLOCK_SIZE            => DESC_BLOCK_SIZE,
      
         -- Internal Bus endpoint generics
         IB_EP_LIMIT                => IB_EP_LIMIT,
         IB_EP_INPUT_BUFFER_SIZE    => IB_EP_INPUT_BUFFER_SIZE,
         IB_EP_OUTPUT_BUFFER_SIZE   => IB_EP_OUTPUT_BUFFER_SIZE,
         IB_EP_READ_REORDER_BUFFER  => IB_EP_READ_REORDER_BUFFER,
         IB_EP_STRICT_EN            => IB_EP_STRICT_EN
      )
      port map (
         -- Common interface
         CLK            => CLK, --: in std_logic;
         RESET          => RESET, --: in std_logic;
         -- RX/TX Interrupts
         RX_INTERRUPT   => RX_INTERRUPT, --: out std_logic;
         TX_INTERRUPT   => TX_INTERRUPT, --: out std_logic;
         
         RX_BUFFER_STATUS  => open,
         RX_BUFFER_FULL    => open,
         RX_BUFFER_EMPTY   => open,
         
         -- network interfaces interface
         -- input FrameLink interface
         RX_SOF_N       => rx_mod_sof_n, --: in  std_logic;
         RX_SOP_N       => rx_mod_sop_n, --: in  std_logic;
         RX_EOF_N       => rx_mod_eof_n, --: in  std_logic;
         RX_EOP_N       => rx_mod_eop_n, --: in  std_logic;
         RX_SRC_RDY_N   => rx_mod_src_rdy_n, --: in  std_logic;
         RX_DST_RDY_N   => rx_mod_dst_rdy_n, --: out std_logic_vector(RX_IFC_COUNT-1 downto 0);
         RX_DATA        => rx_mod_data, --: in  std_logic_vector(RX_DATA_WIDTH-1 downto 0);
         RX_REM         => rx_mod_rem, --: in  std_logic_vector(log2(RX_DATA_WIDTH/8)-1 downto 0);
         RX_ADDR        => rx_mod_addr, --: in  std_logic_vector(abs(log2(RX_IFC_COUNT)-1) downto 0);
         -- output FrameLinks
         TX_SOF_N       => TX_SOF_N, --: out std_logic_vector(TX_IFC_COUNT-1 downto 0);
         TX_SOP_N       => TX_SOP_N, --: out std_logic_vector(TX_IFC_COUNT-1 downto 0);
         TX_EOF_N       => TX_EOF_N, --: out std_logic_vector(TX_IFC_COUNT-1 downto 0);
         TX_EOP_N       => TX_EOP_N, --: out std_logic_vector(TX_IFC_COUNT-1 downto 0);
         TX_SRC_RDY_N   => TX_SRC_RDY_N, --: out std_logic_vector(TX_IFC_COUNT-1 downto 0);
         TX_DST_RDY_N   => TX_DST_RDY_N, --: in  std_logic_vector(TX_IFC_COUNT-1 downto 0);
         TX_DATA        => TX_DATA, --: out std_logic_vector((TX_IFC_COUNT*TX_DATA_WIDTH)-1 downto 0);
         TX_REM         => TX_REM, --: out std_logic_vector(TX_IFC_COUNT*log2(TX_DATA_WIDTH/8)-1 downto 0);
         
         -- Upstream Internal Bus interface
         UP_DATA        => UP_DATA, --: out std_logic_vector(63 downto 0);
         UP_SOP_N       => UP_SOP_N, --: out std_logic;
         UP_EOP_N       => UP_EOP_N, --: out std_logic;
         UP_SRC_RDY_N   => UP_SRC_RDY_N, --: out std_logic;
         UP_DST_RDY_N   => UP_DST_RDY_N, --: in  std_logic;
         
         -- Downstream Internal Bus interface
         DOWN_DATA      => DOWN_DATA, --: in  std_logic_vector(63 downto 0);
         DOWN_SOP_N     => DOWN_SOP_N, --: in  std_logic;
         DOWN_EOP_N     => DOWN_EOP_N, --: in  std_logic;
         DOWN_SRC_RDY_N => DOWN_SRC_RDY_N, --: in  std_logic;
         DOWN_DST_RDY_N => DOWN_DST_RDY_N, --: out std_logic;
         
         -- MI32 Interface
         MI_DWR         => mi32_dwr, --: in  std_logic_vector(31 downto 0);
         MI_ADDR        => mi32_addr, --: in  std_logic_vector(31 downto 0);
         MI_BE          => mi32_be, --: in  std_logic_vector(3 downto 0);
         MI_RD          => mi32_rd, --: in  std_logic;
         MI_WR          => mi32_wr, --: in  std_logic;
         MI_DRDY        => mi32_drdy, --: out std_logic;
         MI_ARDY        => mi32_ardy, --: out std_logic;
         MI_DRD         => mi32_drd --: out std_logic_vector(31 downto 0)        
      );

GEN_FL_MULTIPLEXER_MORE_FLOWS: if DMA_IFC_COUNT > 1 generate

   FL_MULTIPLEXER_I : entity work.FL_MULTIPLEXER
      generic map (
         DATA_WIDTH     => 64,
         CHANNELS       => DMA_IFC_COUNT
      )
      port map (
         CLK            => CLK,
         RESET          => RESET,
         
         RX_SOF_N       => RX_SOF_N,
         RX_SOP_N       => RX_SOP_N,
         RX_EOP_N       => RX_EOP_N,
         RX_EOF_N       => RX_EOF_N,
         RX_SRC_RDY_N   => RX_SRC_RDY_N,
         RX_DST_RDY_N   => RX_DST_RDY_N,
         RX_DATA        => RX_DATA,
         RX_DREM        => RX_REM,
         
         TX_SOF_N       => rx_mod_sof_n,
         TX_EOP_N       => rx_mod_eop_n,
         TX_SOP_N       => rx_mod_sop_n,
         TX_EOF_N       => rx_mod_eof_n,
         TX_SRC_RDY_N   => rx_mod_src_rdy_n,
         TX_DATA        => rx_mod_data,
         TX_DREM        => rx_mod_rem,
         TX_DST_RDY_N   => rx_mod_dst_rdy_n,
         TX_CHANNEL     => rx_mod_addr
      );
      
      --rx_mod_src_rdy_n <= RX_SRC_RDY_N(conv_integer(rx_mod_addr));
      
end generate;

GEN_FL_MULTIPLEXER_ONE_FLOW: if DMA_IFC_COUNT = 1 generate

   rx_mod_sof_n   <= RX_SOF_N(0);
   rx_mod_sop_n   <= RX_SOP_N(0);
   rx_mod_eop_n   <= RX_EOP_N(0);
   rx_mod_eof_n   <= RX_EOF_N(0);
   rx_mod_src_rdy_n <= RX_SRC_RDY_N(0); -- or rx_mod_dst_rdy_n(0);
   RX_DST_RDY_N   <= rx_mod_dst_rdy_n;
   rx_mod_rem     <= RX_REM;
   rx_mod_data    <= RX_DATA;
   rx_mod_addr    <= (others => '0');

end generate;

   LB_ENDPOINT_I : entity work.LB_ENDPOINT_NOREC
      generic map (
         BASE_ADDR   => LB_EP_BASE_ADDR,
         LIMIT       => LB_EP_LIMIT,
         FREQUENCY   => LB_EP_FREQUENCY,
         BUFFER_EN   => LB_EP_BUFFER_EN
      )
      port map (
         LB_CLK      => CLK,
         RESET       => RESET,
         
         LB_DWR      => LB_DWR,
         LB_BE       => LB_BE,
         LB_ADS_N    => LB_ADS_N,
         LB_RD_N     => LB_RD_N,
         LB_WR_N     => LB_WR_N,
         LB_DRD      => LB_DRD,
         LB_RDY_N    => LB_RDY_N,
         LB_ERR_N    => LB_ERR_N,
         LB_ABORT_N  => LB_ABORT_N,
         
         CLK         => CLK,
         MI32_DWR    => mi32_dwr,
         MI32_ADDR   => mi32_addr,
         MI32_RD     => mi32_rd,
         MI32_WR     => mi32_wr,
         MI32_BE     => mi32_be,
         MI32_DRD    => mi32_drd,
         MI32_ARDY   => mi32_ardy,
         MI32_DRDY   => mi32_drdy
      );

end architecture behavioral;
