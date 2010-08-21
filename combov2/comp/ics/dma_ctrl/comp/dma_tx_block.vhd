-- dma_tx_block.vhd: Basic TX block of DMAs with buffers.
-- Copyright (C) 2008 CESNET
-- Author(s): Pavol Korcek <korcek@liberouter.org>
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
--


library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity DMA_TX_BLOCK is
   generic(
      -- number of connected network interfaces 
      -- (same as number of DMA controllers)
      IFC_COUNT         : integer := 4;
      -- data width from/to DMA Buffer
      DATA_WIDTH        : integer := 64;
      -- memory width of DMA requests in DMA ctrl
      DMA_DATA_WIDTH    : integer := 16;
      -- local bus MI address width 
      MI_ADDR_WIDTH     : integer := 6
   );
   port
   (
      -- Common Interface
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- Local Bus (MI32) Interface
      MI_DWR         : in  std_logic_vector(IFC_COUNT*32-1 downto 0);
      MI_ADDR        : in  std_logic_vector(IFC_COUNT*MI_ADDR_WIDTH-1 downto 0); 
      MI_RD          : in  std_logic_vector(IFC_COUNT-1 downto 0);
      MI_WR          : in  std_logic_vector(IFC_COUNT-1 downto 0);
      MI_BE          : in  std_logic_vector(IFC_COUNT*32/8-1 downto 0);
      MI_DRD         : out std_logic_vector(IFC_COUNT*32-1 downto 0);
      MI_ARDY        : out std_logic_vector(IFC_COUNT-1 downto 0);
      MI_DRDY        : out std_logic_vector(IFC_COUNT-1 downto 0);
           
      -- Output FrameLink Interface
      TX_SOF_N       : in  std_logic_vector(IFC_COUNT-1 downto 0);
      TX_SOP_N       : in  std_logic_vector(IFC_COUNT-1 downto 0);
      TX_EOP_N       : in  std_logic_vector(IFC_COUNT-1 downto 0);
      TX_EOF_N       : in  std_logic_vector(IFC_COUNT-1 downto 0);
      TX_SRC_RDY_N   : in  std_logic_vector(IFC_COUNT-1 downto 0);
      TX_DST_RDY_N   : out std_logic_vector(IFC_COUNT-1 downto 0);
      TX_DATA        : in  std_logic_vector(IFC_COUNT*DATA_WIDTH-1 downto 0);
      TX_REM         : in  std_logic_vector(IFC_COUNT*log2(DATA_WIDTH/8)-1 downto 0);

      -- Intenal Bus Write Interface
      IB_WR_ADDR     : in  std_logic_vector(31 downto 0);
      IB_WR_BE       : in  std_logic_vector(7 downto 0);
      IB_WR_REQ      : in  std_logic;
      IB_WR_RDY      : out std_logic;
      IB_WR_DATA     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      
      -- DMA Memory Interface
      DMA_ADDR       : in  std_logic_vector(IFC_COUNT*log2(128/DMA_DATA_WIDTH)-1 downto 0);
      DMA_DOUT       : out std_logic_vector(IFC_COUNT*DMA_DATA_WIDTH-1 downto 0);
      DMA_REQ        : out std_logic_vector(IFC_COUNT-1 downto 0);
      DMA_ACK        : in  std_logic_vector(IFC_COUNT-1 downto 0);
      DMA_DONE       : in  std_logic_vector(IFC_COUNT-1 downto 0);
      DMA_TAG        : in  std_logic_vector(IFC_COUNT*16-1 downto 0);
 
      -- Descriptor Manager Interface
      DESC_READ      : out std_logic_vector(IFC_COUNT-1 downto 0);
      DESC_DO        : in  std_logic_vector(IFC_COUNT*DMA_DATA_WIDTH*-1 downto 0);
      DESC_EMPTY     : in  std_logic_vector(IFC_COUNT-1 downto 0);
      
      -- DMA Control Interface
      INTERRUPT      : out std_logic_vector(IFC_COUNT-1 downto 0); 
      DESC_ENABLE    : out std_logic_vector(IFC_COUNT-1 downto 0);
      
   );
end entity DMA_TX_BLOCK;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of DMA_TX_BLOCK is

   -- ------------------ Constants declaration --------------------------------
      -- buffer memory base
      constant BUFFER_BASE       : std_logic_vector(31 downto 0) := (others => '0');
      -- DMA buffer size
      constant BUFFER_SIZE       : integer := 1024; 
      -- buffer block size (should be a power of 2)
      constant BLOCK_SIZE        : integer := 512;

   -- ------------------ Signals declaration ----------------------------------
      -- Receive buffer interface
      signal buf_newlen          : std_logic_vector(IFC_COUNT*16-1 downto 0);
      signal buf_newlen_dv       : std_logic_vector(IFC_COUNT-1 downto 0);
      signal buf_newlen_rdy      : std_logic_vector(IFC_COUNT-1 downto 0);
      signal buf_rellen          : std_logic_vector(IFC_COUNT*16-1 downto 0);
      signal buf_rellen_dv       : std_logic_vector(IFC_COUNT-1 downto 0);

begin

   assert (DMA_DATA_WIDTH*IFC_COUNT = 64)
      report "DMA_TX_BLOCK: DMA_DATA_WIDTH*IFC_COUNT generics must be equal to 64!"
      severity error;
 
   -- connect TX DMA ctrls
   GEN_RX_DMA_CTRL : for i in 0 to (IFC_COUNT-1) generate
      tx_dma_ctrl_i : entity work.tx_dma_ctrl_opt
         generic map(
               
            BUFFER_ADDR    => BUFFER_BASE + conv_std_logic_vector(i * 16#10000#, 32),           -- FIXME
            BUFFER_SIZE    => BUFFER_SIZE,
            DMA_DATA_WIDTH => DMA_DATA_WIDTH,
            DMA_TAG_ID     => conv_std_logic_vector(2*(IFC_COUNT+i), 8) 
         )
         port map(
               
            -- Common Interface
            CLK            => CLK,
            RESET          => RESET,
            INTERRUPT      => INTERRUPT(i),
            ENABLE         => ENABLE(i),

            -- Receive Buffer Interface
            BUF_NEWLEN     => buf_newlen((i+1)*16-1 downto i*16),
            BUF_NEWLEN_DV  => buf_newlen_dv(i),
            BUF_NEWLEN_RDY => buf_newlen_rdy(i),
            BUF_RELLEN     => buf_rellen((i+1)*16-1 downto i*16),
            BUF_RELLEN_DV  => buf_rellen_dv(i),
         
            -- Descriptor Interface
            DESC_READ      => DESC_READ(i),
            DESC_DO        => DESC_DO((i+1)*DMA_DATA_WIDTH-1 downto i*DMA_DATA_WIDTH),
            DESC_EMPTY     => DESC_EMPTY(i),;

            -- Memory Interface
            SW_DWR         => SW_DWR((i+1)*32-1 downto i*32),
            SW_ADDR        => SW_ADDR((i+1)*MI_ADDR_WIDTH-1 downto i*MI_ADDR_WIDTH), 
            SW_RD          => SW_RD(i),
            SW_WR          => SW_WR(i),
            SW_BE          => SW_BE((i+1)*32/8-1 downto i*32/8),
            SW_DRD         => SW_DRD((i+1)*32-1 downto i*32),
            SW_ARDY        => SW_ARDY(i),
            SW_DRDY        => SW_DRDY(i),     
            
            -- DMA Interface
            DMA_ADDR       => DMA_ADDR((i+1)*log2(128/DMA_DATA_WIDTH)-1 downto i*log2(128/DMA_DATA_WIDTH)),
            DMA_DOUT       => DMA_DOUT((i+1)*DMA_DATA_WIDTH-1 downto i*DMA_DATA_WIDTH),
            DMA_REQ        => DMA_REQ(i),
            DMA_ACK        => DMA_ACK(i),
            DMA_DONE       => DMA_DONE(i),
            DMA_TAG        => DMA_TAG((i+1)*16-1 downto i*16)
         );
         
   -- connect TX DMA buffer
   TX_BUF : entity work.SW_TXBUF_TOP
      generic map(
            
         -- Input data width
         DATA_WIDTH     => DATA_WIDTH,
         -- Block size
         BLOCK_SIZE     => BLOCK_SIZE,
         -- Number of flows
         FLOWS          => IFC_COUNT
         )          
      port map(
            
         -- Common Interface
         CLK            => CLK,
         RESET          => RESET,
         
         -- Output FrameLink Interface
         TX_SOF_N       => TX_SOF_N,
         TX_SOP_N       => TX_SOP_N,
         TX_EOP_N       => TX_EOP_N,
         TX_EOF_N       => TX_EOF_N,
         TX_SRC_RDY_N   => TX_SRC_RDY_N,
         TX_DST_RDY_N   => TX_DST_RDY_N,
         TX_DATA        => TX_DATA,
         TX_REM         => TX_REM,
         
         -- Memory Write Interface
         WR_ADDR        => IB_WR_ADDR,
         WR_BE          => IB_WR_BE,
         WR_REQ         => IB_WR_REQ,
         WR_RDY         => IB_WR_ARDY,
         WR_DATA        => IB_WR_DATA,
         
         -- Transmit Buffer Interface
         TX_NEWLEN      => buf_newlen,
         TX_NEWLEN_DV   => buf_newlen_dv,
         TX_NEWLEN_RDY  => buf_newlen_rdy,
         TX_RELLEN      => buf_rellen,
         TX_RELLEN_DV   => buf_rellen_dv
      );

end architecture full; 

