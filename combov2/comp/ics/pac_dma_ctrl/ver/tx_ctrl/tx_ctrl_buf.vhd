-- tx_ctrl_buf.vhd: TX DMA controller and TX buffer top cover 
-- Copyright (C) 2009 CESNET
-- Author(s): Petr Kastovsky <kastovsky@liberouter.org>
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

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- package with log2 function
use work.math_pack.all;
use work.pac_dma_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity tx_ctrl_buf_pac is
   generic (
      -- ============= common generics ================
      FLOWS             : integer := 2;
      -- ============= RX BUFFER generics ================
      -- Internal Bus data width
      BUFFER_DATA_WIDTH       : integer := 64;
      -- available space in the RX buffer for each flow
      BUFFER_BLOCK_SIZE       : integer := 512;
      -- total size of the RX buffer for on flow is BUFFER_DATA_WIDTH * BUFFER_BLOCK_SIZE [bit]

      -- total size [bytes] for one flow (interface)
      BUFFER_TOTAL_FLOW_SIZE  : integer := 16384;

      -- ============ RX CTRL generics ===============
      -- address of first rx buffer
      CTRL_BUFFER_ADDR    : std_logic_vector(31 downto 0) := X"00000000";
      -- address gap between two rx buffers
      CTRL_BUFFER_GAP     : std_logic_vector(31 downto 0) := X"00008000";
      -- size of rx buffer
      CTRL_BUFFER_SIZE    : integer := 1024;
      -- tag for bus master operations
      CTRL_DMA_ID         : std_logic_vector(1 downto 0) := "10";
      -- dma data width - output width of dma request
      CTRL_DMA_DATA_WIDTH    : integer := 32;
      -- size of inner fifo
      CTRL_BLOCK_SIZE     : integer := 4

   );
   port (
      -- common interface
      CLK         : in  std_logic;
      RESET       : in  std_logic;

      -- misc signals
      RUN    : in  std_logic_vector(FLOWS-1 downto 0);
      IDLE   : out std_logic_vector(FLOWS-1 downto 0);

      -- descriptor FIFO interface
      DESC_READ   : out std_logic;
      DESC_ADDR   : out std_logic_vector(log2(FLOWS)-1 downto 0);
      DESC_DO     : in  std_logic_vector(63 downto 0);
      DESC_DO_VLD : in  std_logic;
      DESC_EMPTY  : in  std_logic_vector(FLOWS-1 downto 0);

      -- DMA Interface
      DMA_ADDR    : in  std_logic_vector(log2(128/CTRL_DMA_DATA_WIDTH)-1 downto 0);
      DMA_DOUT    : out std_logic_vector(CTRL_DMA_DATA_WIDTH-1 downto 0);
      DMA_REQ     : out std_logic;
      DMA_ACK     : in  std_logic;
      DMA_DONE    : in  std_logic;
      DMA_TAG     : in  std_logic_vector(15 downto 0);

      -- Status update
      SU_ADDR        : out std_logic_vector(abs(log2(FLOWS)-1) downto 0);
      -- data width should change
      SU_DATA        : out std_logic_vector(NUM_FLAGS-1 downto 0);
      SU_DATA_VLD    : out std_logic;
      SU_HFULL       : in  std_logic_vector(FLOWS-1 downto 0);

      -- Write interface (InternalBus)
      WR_ADDR     : in  std_logic_vector(31 downto 0);
      WR_BE       : in  std_logic_vector(7 downto 0);
      WR_REQ      : in  std_logic;
      WR_RDY      : out std_logic;
      WR_DATA     : in  std_logic_vector(BUFFER_DATA_WIDTH-1 downto 0);
       
      -- Read interface (FrameLinks)
      TX_DATA       : out std_logic_vector(BUFFER_DATA_WIDTH-1 downto 0);
      TX_SOF_N      : out std_logic_vector(FLOWS-1 downto 0);
      TX_SOP_N      : out std_logic_vector(FLOWS-1 downto 0);
      TX_EOP_N      : out std_logic_vector(FLOWS-1 downto 0);
      TX_EOF_N      : out std_logic_vector(FLOWS-1 downto 0);
      TX_REM        : out std_logic_vector(
         abs((log2((BUFFER_DATA_WIDTH/FLOWS)/8)*FLOWS)-1) downto 0);
      TX_SRC_RDY_N  : out std_logic_vector(FLOWS-1 downto 0);
      TX_DST_RDY_N  : in  std_logic_vector(FLOWS-1 downto 0)

   );
end entity tx_ctrl_buf_pac;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of tx_ctrl_buf_pac is

  -- interface between TX DMA controllers and TX buffer
  signal tx_buf_newlen      : std_logic_vector(FLOWS*16-1 downto 0);
  signal tx_buf_newlen_dv   : std_logic_vector(FLOWS-1 downto 0);
  signal tx_buf_newlen_rdy  : std_logic_vector(FLOWS-1 downto 0);
  signal tx_buf_rellen      : std_logic_vector(FLOWS*16-1 downto 0);
  signal tx_buf_rellen_dv   : std_logic_vector(FLOWS-1 downto 0);

  -- internal bus write address and write request
  signal ib_addr            : std_logic_vector(31 downto 0);
  signal ib_wr_req          : std_logic;

  -- helpful signal: correct address on internal bus
  signal ib_correct_addr    : std_logic_vector(31 downto 0);

begin

   -- InternalBus address
   ib_addr(19 downto 0)  <= WR_ADDR(19 downto 0);
   ib_addr(31 downto 20) <= (others => '0');

   -- the address that should be on the InternalBus to target the TX buffer
   ib_correct_addr <= CTRL_BUFFER_ADDR;

   -- multiplexer that switches internal bus write requests
   ib_wr_req <= WR_REQ when (WR_ADDR(31 downto 20) = ib_correct_addr(31 downto 20))
                else '0';

   TX_CTRL_I : entity work.tx_ctrl
   generic map(
      BUFFER_ADDR    => CTRL_BUFFER_ADDR,
      BUFFER_GAP     => CTRL_BUFFER_GAP,
      BUFFER_SIZE    => CTRL_BUFFER_SIZE,
      DMA_ID         => CTRL_DMA_ID,
      DMA_DATA_WIDTH => CTRL_DMA_DATA_WIDTH,
      CHANNELS       => FLOWS,
      BLOCK_SIZE     => CTRL_BLOCK_SIZE
   )
   port map(
      -- Common interface
      CLK         => CLK,
      RESET       => RESET,
   
      RUN         => RUN,
      IDLE        => IDLE,

      -- TX buffer interface
      BUF_NEWLEN     => tx_buf_newlen,
      BUF_NEWLEN_DV  => tx_buf_newlen_dv,
      BUF_NEWLEN_RDY => tx_buf_newlen_rdy,
      BUF_RELLEN     => tx_buf_rellen,
      BUF_RELLEN_DV  => tx_buf_rellen_dv,

      -- descriptor fifo interface
      DESC_READ   => DESC_READ,
      DESC_ADDR   => DESC_ADDR,
      DESC_DO     => DESC_DO,
      DESC_DO_VLD => DESC_DO_VLD,
      DESC_EMPTY  => DESC_EMPTY,

      -- DMA Interface
      DMA_ADDR   => DMA_ADDR,
      DMA_DOUT   => DMA_DOUT,
      DMA_REQ    => DMA_REQ,
      DMA_ACK    => DMA_ACK,
      DMA_DONE   => DMA_DONE,
      DMA_TAG    => DMA_TAG,

      -- Status update
      SU_ADDR        => SU_ADDR,
      -- data width should change
      SU_DATA        => SU_DATA,
      SU_DATA_VLD    => SU_DATA_VLD,
      SU_HFULL       => SU_HFULL

   );

   TX_BUFFER_I : entity work.SW_TXBUF_PAC_TOP
   generic map(
     DATA_WIDTH       => BUFFER_DATA_WIDTH,
     BLOCK_SIZE       => BUFFER_BLOCK_SIZE,
     FLOWS            => FLOWS,
     TOTAL_FLOW_SIZE  => BUFFER_TOTAL_FLOW_SIZE
   )
   port map(
     -- Common interface
     CLK              => CLK,
     RESET            => RESET,

     -- Write interface (InternalBus)
     WR_ADDR          => ib_addr,
     WR_BE            => WR_BE,
     WR_REQ           => ib_wr_req,
     WR_RDY           => WR_RDY,
     WR_DATA          => WR_DATA,

     -- TX controller interface
     TX_NEWLEN        => tx_buf_newlen,
     TX_NEWLEN_DV     => tx_buf_newlen_dv,
     TX_NEWLEN_RDY    => tx_buf_newlen_rdy,
     TX_RELLEN        => tx_buf_rellen,
     TX_RELLEN_DV     => tx_buf_rellen_dv,
    
     -- Read interface (FrameLinks)
     TX_DATA          => TX_DATA,
     TX_SOF_N         => TX_SOF_N,
     TX_SOP_N         => TX_SOP_N,
     TX_EOP_N         => TX_EOP_N,
     TX_EOF_N         => TX_EOF_N,
     TX_REM           => TX_REM,
     TX_SRC_RDY_N     => TX_SRC_RDY_N,
     TX_DST_RDY_N     => TX_DST_RDY_N

   );

end architecture full;
