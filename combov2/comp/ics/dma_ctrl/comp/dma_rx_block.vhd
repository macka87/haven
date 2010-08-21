-- dma_rx_block.vhd: Basic RX block of DMAs with buffers.
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
entity DMA_RX_BLOCK is
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
           
      -- Input FrameLink Interface
      RX_SOF_N       : in  std_logic_vector(IFC_COUNT-1 downto 0);
      RX_SOP_N       : in  std_logic_vector(IFC_COUNT-1 downto 0);
      RX_EOP_N       : in  std_logic_vector(IFC_COUNT-1 downto 0);
      RX_EOF_N       : in  std_logic_vector(IFC_COUNT-1 downto 0);
      RX_SRC_RDY_N   : in  std_logic_vector(IFC_COUNT-1 downto 0);
      RX_DST_RDY_N   : out std_logic_vector(IFC_COUNT-1 downto 0);
      RX_DATA        : in  std_logic_vector(IFC_COUNT*DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(IFC_COUNT*log2(DATA_WIDTH/8)-1 downto 0);

      -- Intenal Bus Read Interface
      IB_RD_ADDR     : in  std_logic_vector(31 downto 0);
      IB_RD_BE       : in  std_logic_vector(7 downto 0);
      IB_RD_REQ      : in  std_logic;
      IB_RD_ARDY     : out std_logic;
      IB_RD_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);
      IB_RD_SRC_RDY  : out std_logic;
      IB_RD_DST_RDY  : in  std_logic;
      
      -- DMA Memory Interface
      DMA_ADDR       : in  std_logic_vector(IFC_COUNT*log2(128/DMA_DATA_WIDTH)-1 downto 0);
      DMA_DOUT       : out std_logic_vector(IFC_COUNT*DMA_DATA_WIDTH-1 downto 0);
      DMA_REQ        : out std_logic_vector(IFC_COUNT-1 downto 0);
      DMA_ACK        : in  std_logic_vector(IFC_COUNT-1 downto 0);
      DMA_DONE       : in  std_logic_vector(IFC_COUNT-1 downto 0);
      DMA_TAG        : in  std_logic_vector(IFC_COUNT*16-1 downto 0);
 
      -- Descriptor Manager Interface
      DESC_READ      : out std_logic_vector(IFC_COUNT-1 downto 0);
      DESC_DO        : in  std_logic_vector(IFC_COUNT*DMA_DATA_WIDTH-1 downto 0);
      DESC_EMPTY     : in  std_logic_vector(IFC_COUNT-1 downto 0);
      
      -- DMA Control Interface
      INTERRUPT      : out std_logic_vector(IFC_COUNT-1 downto 0); 
      DESC_ENABLE    : out std_logic_vector(IFC_COUNT-1 downto 0);
      
   );
end entity DMA_RX_BLOCK;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of DMA_RX_BLOCK is

   -- ------------------ Constants declaration --------------------------------
      -- buffer memory base
      constant BUFFER_BASE       : std_logic_vector(31 downto 0) := (others => '0');
      -- DMA memory base
      constant DMA_BASE          : std_logic_vector(31 downto 0) := (others => '0');
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
      report "DMA_RX_BLOCK: DMA_DATA_WIDTH*IFC_COUNT generics must be equal to 64!"
      severity error;
 
   -- connect RX DMA ctrls
   GEN_RX_DMA_CTRL : for i in 0 to (IFC_COUNT-1) generate
      rx_dma_ctrl_i : entity work.rx_dma_ctrl_opt
         generic map(
               
            BASE_ADDR      => DMA_BASE + conv_std_logic_vector(i * 16#40#, 32),           -- FIXME
            BUFFER_ADDR    => BUFFER_BASE + conv_std_logic_vector(i * 16#4000#, 32),      -- FIXME
            BUFFER_SIZE    => BUFFER_SIZE,
            DMA_DATA_WIDTH => DMA_DATA_WIDTH,
            DMA_TAG_ID     => conv_std_logic_vector(2*i, 8) 
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
         
   -- connect RX DMA buffer
   RX_BUF : entity work.SW_RXBUF_TOP
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
         
         -- Input FrameLink Interface
         RX_SOF_N       => RX_SOF_N,
         RX_SOP_N       => RX_SOP_N,
         RX_EOP_N       => RX_EOP_N,
         RX_EOF_N       => RX_EOF_N,
         RX_SRC_RDY_N   => RX_SRC_RDY_N,
         RX_DST_RDY_N   => RX_DST_RDY_N,
         RX_DATA        => RX_DATA,
         RX_REM         => RX_REM,
         
         -- Memory Read Interface
         RD_ADDR        => IB_RD_ADDR,
         RD_BE          => IB_RD_BE,
         RD_REQ         => IB_RD_REQ,
         RD_ARDY        => IB_RD_ARDY,
         RD_DATA        => IB_RD_DATA,
         RD_SRC_RDY     => IB_RD_SRC_RDY,
         RD_DST_RDY     => IB_RD_DST_RDY,
         
         -- Receive Buffer Interface
         RX_NEWLEN      => buf_newlen,
         RX_NEWLEN_DV   => buf_newlen_dv,
         RX_NEWLEN_RDY  => buf_newlen_rdy,
         RX_RELLEN      => buf_rellen,
         RX_RELLEN_DV   => buf_rellen_dv
      );

end architecture full; 
