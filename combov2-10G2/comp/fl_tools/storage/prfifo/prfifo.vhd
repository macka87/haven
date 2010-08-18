--
-- prfifo.vhd: Packet Release FIFO
-- Copyright (C) 2007 CESNET
-- Author(s): Koritak Jan <jenda@liberouter.org>
--            Vozenilek Jan <xvozen00@stud.fit.vutbr.cz>
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
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- library containing log2 function
use work.math_pack.all;

-- FIFO package
use work.fifo_pkg.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of FL_PRFIFO is

   constant REM_WIDTH        : integer := log2(DATA_WIDTH/8);

   -- FIFO item consists of DATA, REM and FL_JUICE signals
   constant ITEM_WIDTH       : integer := DATA_WIDTH + REM_WIDTH + 1;

   -- JUICE and REM positions in FIFO item
   constant JUICE_POS        : integer := DATA_WIDTH;
   constant REM_POS          : integer := DATA_WIDTH + 1;

   -- bit-range of REM slice in FIFO item
   subtype  REM_RANGE       is natural range REM_POS + REM_WIDTH - 1 downto REM_POS;
   subtype  DATA_RANGE      is natural range DATA_WIDTH - 1 downto 0;

   -- FIFO memory input and output
   signal   sig_item_out     : std_logic_vector(ITEM_WIDTH-1 downto 0);
   signal   sig_item_in      : std_logic_vector(ITEM_WIDTH-1 downto 0);

   -- FIFO memory control signals
   signal   sig_fifo_rd      : std_logic;
   signal   sig_fifo_wr      : std_logic;

   signal   sig_fifo_valid   : std_logic;

   signal   sig_fifo_full    : std_logic;
   signal   sig_fifo_wr_disc : std_logic;

   signal   sig_blk_end      : std_logic;

   -- Compress/decompress partcount detection signal
   signal   sig_frame_part   : std_logic;

   -- Flow control of output interface
   signal   sig_tx_src_rdy_n : std_logic;

begin
   -- Block FIFO memory instance

   fifo : entity work.FIFO_SYNC_BLOCK
   generic map (
      -- type of main FIFO memory
      MAIN_MEM   => MEM_TYPE,
      -- type of address FIFO memory
      ADDR_MEM   => LUT,
      LATENCY    => 1,
      ITEMS      => ITEMS,
      ITEM_WIDTH => ITEM_WIDTH,
      BLOCK_TYPE => VARIABLE_SIZE,
      -- maximum block to be stored (size of address FIFO) - recommended is ITEMS
      MAX_BLOCKS => ITEMS,
      DISCARD    => WriteDiscard,
      PREFETCH   => true
   )
   port map (
      CLK          => CLK,
      RESET        => RESET,

      WR           => sig_fifo_wr,
      DI           => sig_item_in,

      RD           => sig_fifo_rd,
      DO           => sig_item_out,
      DO_DV        => sig_fifo_valid,

      FULL         => sig_fifo_full,
      EMPTY        => open,

      BLK_END      => sig_blk_end,       
      BLK_READY    => open,
      BLK_FINISH   => open,

      WR_DISCARD   => sig_fifo_wr_disc,

      RD_DISCARD   => '0'
   );

   -- Compressing unit instance

   compress : entity work.FL_COMPRESS
   generic map (
      WIRES        => 1
   )
   port map (
      CLK          => CLK,
      RESET        => RESET,

      RX_SRC_RDY_N => RX_SRC_RDY_N,
      RX_DST_RDY_N => '0', 

      RX_SOP_N     => RX_SOP_N,
      RX_EOP_N     => RX_EOP_N,
      RX_SOF_N     => RX_SOF_N,
      RX_EOF_N     => RX_EOF_N,

      FRAME_PART   => sig_frame_part,

      FL_JUICE     => sig_item_in(JUICE_POS downto JUICE_POS)
   );

   -- Decompressing unit instance

   decompress : entity work.FL_DECOMPRESS
   generic map (
      WIRES        => 1,
      PARTS        => PARTS
   )
   port map (
      CLK          => CLK,
      RESET        => RESET,

      TX_SRC_RDY_N => sig_tx_src_rdy_n,
      TX_DST_RDY_N => TX_DST_RDY_N,

      TX_SOP_N     => TX_SOP_N,
      TX_EOP_N     => TX_EOP_N,
      TX_SOF_N     => TX_SOF_N,
      TX_EOF_N     => TX_EOF_N,

      DISCARD      => '0',
      FRAME_PART   => sig_frame_part,

      FL_JUICE     => sig_item_out(JUICE_POS downto JUICE_POS)
   );

   -- Flow control

   sig_tx_src_rdy_n <= not sig_fifo_valid;

   RX_DST_RDY_N <= '0';
   TX_SRC_RDY_N <= sig_tx_src_rdy_n;

   -- FIFO Data mapping
   
   sig_item_in(DATA_RANGE) <= RX_DATA;
   sig_item_in(REM_RANGE)  <= RX_REM;

   TX_DATA <= sig_item_out(DATA_RANGE);
   TX_REM  <= sig_item_out(REM_RANGE);

   -- FIFO control

   sig_fifo_wr_disc <= sig_fifo_full and (not RX_SRC_RDY_N);

   sig_fifo_wr <= not RX_SRC_RDY_N;
   sig_fifo_rd <= not TX_DST_RDY_N;

   sig_blk_end <= not RX_EOF_N;
   
end architecture;
