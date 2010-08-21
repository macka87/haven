-- pfifo_fl8.vhd: Frame Link protocol generic packet FIFO wrapper
-- Copyright (C) 2007 CESNET
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

-- library containing log2 function
use work.math_pack.all;
-- library with t_flxx data types
use work.fl_pkg.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_PFIFO_FL8 is
   generic(
      -- number of items in the FIFO
      ITEMS          : integer;
      -- Size of block (for LSTBLK signal)
      BLOCK_SIZE     : integer;
      -- Width of STATUS signal available
      STATUS_WIDTH   : integer;
      -- Maximal number of packets
      MAX_DISCARD_BLOCKS : integer;
      -- Number of parts in each frame
      PARTS          : integer
   );
   port(
      -- Common signals
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- FrameLink interfaces
      RX             : inout t_fl8;
      TX             : inout t_fl8;

      -- FIFO control signals
      DISCARD        : in  std_logic;
      LSTBLK         : out std_logic;
      FULL           : out std_logic;
      EMPTY          : out std_logic;
      STATUS         : out std_logic_vector(STATUS_WIDTH-1 downto 0);
      FRAME_RDY      : out std_logic
   );
end entity FL_PFIFO_FL8;      

architecture full of FL_PFIFO_FL8 is
begin
   
   FL_FIFO_I: entity work.FL_PFIFO8
   generic map
   (
      ITEMS       => ITEMS,
      BLOCK_SIZE  => BLOCK_SIZE,
      STATUS_WIDTH=> STATUS_WIDTH,
      MAX_DISCARD_BLOCKS => MAX_DISCARD_BLOCKS,
      PARTS       => PARTS
   )
   port map
   (
      CLK            => CLK,
      RESET          => RESET,

      -- write interface
      RX_DATA        => RX.DATA,
      RX_SRC_RDY_N   => RX.SRC_RDY_N,
      RX_DST_RDY_N   => RX.DST_RDY_N,
      RX_SOP_N       => RX.SOP_N,
      RX_EOP_N       => RX.EOP_N,
      RX_SOF_N       => RX.SOF_N,
      RX_EOF_N       => RX.EOF_N,
      
      -- read interface
      TX_DATA        => TX.DATA,
      TX_SRC_RDY_N   => TX.SRC_RDY_N,
      TX_DST_RDY_N   => TX.DST_RDY_N,
      TX_SOP_N       => TX.SOP_N,
      TX_EOP_N       => TX.EOP_N,
      TX_SOF_N       => TX.SOF_N,
      TX_EOF_N       => TX.EOF_N,

      -- FIFO state signals
      DISCARD        => DISCARD,
      LSTBLK         => LSTBLK,
      FULL           => FULL,
      EMPTY          => EMPTY,
      STATUS         => STATUS,
      FRAME_RDY      => FRAME_RDY
   );

end architecture full;
