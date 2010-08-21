-- binder.vhd: FrameLink Binder top architecture
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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

-- Binder declarations
use work.fl_binder_decl.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_BINDER is
begin

   -- generate SIMPLE Binder
   GEN_SIMPLE_BINDER: if SIMPLE_BINDER and not STUPID_BINDER generate
      FL_BINDER : entity work.FL_BINDER_SIMPLE
         generic map(
            INPUT_WIDTH    => INPUT_WIDTH,
            INPUT_COUNT    => INPUT_COUNT,
            OUTPUT_WIDTH   => OUTPUT_WIDTH,
            FRAME_PARTS    => FRAME_PARTS,
            QUEUE_CHOOSING => QUEUE_CHOOSING
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- input FrameLink interface
            RX_SOF_N       => RX_SOF_N,
            RX_SOP_N       => RX_SOP_N,
            RX_EOP_N       => RX_EOP_N,
            RX_EOF_N       => RX_EOF_N,
            RX_SRC_RDY_N   => RX_SRC_RDY_N,
            RX_DST_RDY_N   => RX_DST_RDY_N,
            RX_DATA        => RX_DATA,
            RX_REM         => RX_REM,
            -- output FrameLink interface
            TX_SOF_N       => TX_SOF_N,
            TX_SOP_N       => TX_SOP_N,
            TX_EOP_N       => TX_EOP_N,
            TX_EOF_N       => TX_EOF_N,
            TX_SRC_RDY_N   => TX_SRC_RDY_N,
            TX_DST_RDY_N   => TX_DST_RDY_N,
            TX_DATA        => TX_DATA,
            TX_REM         => TX_REM
         );
   end generate;

   
   -- generate STUPID Binder
   GEN_STUPID_BINDER: if STUPID_BINDER and not SIMPLE_BINDER generate
      FL_BINDER : entity work.FL_BINDER_STUPID
         generic map(
            INPUT_WIDTH    => INPUT_WIDTH,
            INPUT_COUNT    => INPUT_COUNT,
            OUTPUT_WIDTH   => OUTPUT_WIDTH,
            FRAME_PARTS    => FRAME_PARTS
            -- QUEUE_CHOOSING => QUEUE_CHOOSING
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- input FrameLink interface
            RX_SOF_N       => RX_SOF_N,
            RX_SOP_N       => RX_SOP_N,
            RX_EOP_N       => RX_EOP_N,
            RX_EOF_N       => RX_EOF_N,
            RX_SRC_RDY_N   => RX_SRC_RDY_N,
            RX_DST_RDY_N   => RX_DST_RDY_N,
            RX_DATA        => RX_DATA,
            RX_REM         => RX_REM,
            -- output FrameLink interface
            TX_SOF_N       => TX_SOF_N,
            TX_SOP_N       => TX_SOP_N,
            TX_EOP_N       => TX_EOP_N,
            TX_EOF_N       => TX_EOF_N,
            TX_SRC_RDY_N   => TX_SRC_RDY_N,
            TX_DST_RDY_N   => TX_DST_RDY_N,
            TX_DATA        => TX_DATA,
            TX_REM         => TX_REM
         );
   end generate;

   -- generate NFIFO2FIFO Binder
   GEN_NFIFO2FIFO_BINDER: if not SIMPLE_BINDER and not STUPID_BINDER  generate
      FL_BINDER : entity work.FL_BINDER_NFIFO2FIFO
         generic map(
            INPUT_WIDTH    => INPUT_WIDTH,
            INPUT_COUNT    => INPUT_COUNT,
            OUTPUT_WIDTH   => OUTPUT_WIDTH,
            LUT_MEMORY     => LUT_MEMORY,
            LUT_BLOCK_SIZE => LUT_BLOCK_SIZE,
            FRAME_PARTS    => FRAME_PARTS,
            QUEUE_CHOOSING => QUEUE_CHOOSING
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- input FrameLink interface
            RX_SOF_N       => RX_SOF_N,
            RX_SOP_N       => RX_SOP_N,
            RX_EOP_N       => RX_EOP_N,
            RX_EOF_N       => RX_EOF_N,
            RX_SRC_RDY_N   => RX_SRC_RDY_N,
            RX_DST_RDY_N   => RX_DST_RDY_N,
            RX_DATA        => RX_DATA,
            RX_REM         => RX_REM,
            -- output FrameLink interface
            TX_SOF_N       => TX_SOF_N,
            TX_SOP_N       => TX_SOP_N,
            TX_EOP_N       => TX_EOP_N,
            TX_EOF_N       => TX_EOF_N,
            TX_SRC_RDY_N   => TX_SRC_RDY_N,
            TX_DST_RDY_N   => TX_DST_RDY_N,
            TX_DATA        => TX_DATA,
            TX_REM         => TX_REM
         );
   end generate;

end architecture full;
