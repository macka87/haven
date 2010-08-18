-- pfifo_arch_full.vhd: Frame Link protocol generic packet FIFO (full arch)
-- Copyright (C) 2006 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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

-- library containing log2 and min functions
use work.math_pack.all;

-- library with get_juice_width function
use work.fl_fifo_pkg.all;

architecture full of FL_PFIFO is

component fifo_bram_discard is
   generic(
      -- ITEMS = Numer of items in FIFO
      ITEMS       : integer;

      -- BLOCK_SIZE = Number of items in one block
      BLOCK_SIZE  : integer := 0;

      -- Block Ram Type, only 1, 2, 4, 9, 18, 36 bits
      BRAM_TYPE   : integer := 36;

      -- Data Width, DATA_WIDTH mod BRAM_TYPE must be 0
      DATA_WIDTH  : integer;

      STATUS_WIDTH: integer := 4;
      
      -- AUTO_PIPELINE:boolean := false

      -- Maximal blocks
      MAX_DISCARD_BLOCKS : integer := 10
   );
   port(
      CLK      : in  std_logic;
      RESET    : in  std_logic;

      -- Write interface
      WR       : in  std_logic;
      EOB      : in  std_logic;
      DI       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      FULL     : out std_logic;
      LSTBLK   : out std_logic;
      STATUS   : out std_logic_vector(STATUS_WIDTH-1 downto 0);

      -- Read interface
      RD       : in  std_logic;
      DISCARD  : in  std_logic;
      DO       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      DV       : out std_logic;
      EMPTY    : out std_logic;
      FRAME_RDY: out std_logic
   );
end component fifo_bram_discard;

-- Constants declaration

-- Compute width of FL_JUICE signal
constant JUICE_WIDTH : integer := get_juice_width(DATA_WIDTH, true);

constant MEM_WIDTH : integer := DATA_WIDTH+log2(DATA_WIDTH/8)+JUICE_WIDTH;
                           --   DATA       REM                FL_JUICE

-- Signals declaration
signal sig_fifo_eob  : std_logic;   -- End of block detection for FIFO
signal sig_full      : std_logic;   -- FIFO is full
signal sig_empty     : std_logic;   -- FIFO is empty
signal sig_status    : std_logic_vector(STATUS_WIDTH-1 downto 0); -- Free items
signal sig_vld       : std_logic;   -- Data valid at the output of the fifo
signal sig_tx_src_rdy_n:std_logic;
signal sig_rd        : std_logic;   -- Read from FIFO
signal sig_wr        : std_logic;   -- Write to FIFO
signal sig_data_rd   : std_logic_vector(MEM_WIDTH-1 downto 0); -- data from FIFO
signal sig_data_wr   : std_logic_vector(MEM_WIDTH-1 downto 0); -- data from FIFO

signal sig_sof_n_rd  : std_logic;   -- Start of frame at the output
signal sig_sop_n_rd  : std_logic;   -- Start of packet at the output
signal sig_eop_n_rd  : std_logic;   -- End of packet at the output
signal sig_eof_n_rd  : std_logic;   -- End of frame at the output

signal sig_juice_in  : std_logic_vector(JUICE_WIDTH-1 downto 0);
signal sig_juice_out : std_logic_vector(JUICE_WIDTH-1 downto 0);
signal sig_frame_part: std_logic;

begin

sig_rd      <= (not TX_DST_RDY_N) or not sig_vld;
sig_wr      <= (not RX_SRC_RDY_N) and not sig_full;

sig_tx_src_rdy_n <= not sig_vld;

sig_data_wr <= sig_juice_in & RX_REM & RX_DATA;

-- Compress FrameLink control signals to sig_juice_in
fl_compress_inst : entity work.fl_compress
generic map(
   WIRES       => JUICE_WIDTH
)
port map(
   CLK         => CLK,
   RESET       => RESET,

   RX_SRC_RDY_N=> RX_SRC_RDY_N,
   RX_DST_RDY_N=> sig_full,
   RX_SOP_N    => RX_SOP_N,
   RX_EOP_N    => RX_EOP_N,
   RX_SOF_N    => RX_SOF_N,
   RX_EOF_N    => RX_EOF_N,
   FL_JUICE    => sig_juice_in,
   FRAME_PART  => sig_frame_part
);

-- Decompress FrameLink signals from sig_juice_out
fl_decompress_inst : entity work.fl_decompress_any
generic map(
   WIRES    => JUICE_WIDTH,
   PARTS    => PARTS
)
port map(
   -- Common interface
   CLK         => CLK,
   RESET       => RESET,
      
   TX_SRC_RDY_N=> sig_tx_src_rdy_n,
   TX_DST_RDY_N=> TX_DST_RDY_N,
   TX_SOP_N    => sig_sop_n_rd,
   TX_EOP_N    => sig_eop_n_rd,
   TX_SOF_N    => sig_sof_n_rd,
   TX_EOF_N    => sig_eof_n_rd,
   FL_JUICE    => sig_juice_out,
   DISCARD     => DISCARD
);

-- Store whole FrameLink protocol flow in the FIFO
fifo_inst: fifo_bram_discard
generic map(
   ITEMS       => ITEMS,
   BLOCK_SIZE  => BLOCK_SIZE,
   BRAM_TYPE   => get_bram_type(DATA_WIDTH),
   STATUS_WIDTH=> STATUS_WIDTH,
   DATA_WIDTH  => MEM_WIDTH
)
port map(
   RESET       => RESET,
   CLK         => CLK,

   -- Write interface
   DI          => sig_data_wr,
   EOB         => sig_fifo_eob,
   WR          => sig_wr,
   FULL        => sig_full,
   LSTBLK      => LSTBLK,
   STATUS      => sig_status,

   -- Read interface
   DO          => sig_data_rd,
   DISCARD     => DISCARD,
   RD          => sig_rd,
   EMPTY       => sig_empty,
   DV          => sig_vld,
   FRAME_RDY   => FRAME_RDY
);
   
sig_fifo_eob <= not RX_EOF_N;

RX_DST_RDY_N  <= sig_full or RESET;
TX_SRC_RDY_N  <= sig_tx_src_rdy_n;

TX_DATA     <= sig_data_rd(DATA_WIDTH-1 downto 0);
TX_REM      <= sig_data_rd(DATA_WIDTH+log2(DATA_WIDTH/8)-1 downto DATA_WIDTH);
sig_juice_out<=sig_data_rd(MEM_WIDTH-1 downto MEM_WIDTH-JUICE_WIDTH);

TX_SOF_N <= sig_sof_n_rd;
TX_EOF_N <= sig_eof_n_rd;
TX_SOP_N <= sig_sop_n_rd;
TX_EOP_N <= sig_eop_n_rd;

EMPTY    <= sig_empty;
FULL     <= sig_full;
STATUS   <= sig_status;
end architecture full;
