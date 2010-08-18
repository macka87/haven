-- splitter.vhd: FrameLink Splitter architecture
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
use work.math_pack.all;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_SPLITTER is

   -- ------------------ Constants declaration --------------------------------
   constant STATUS_WIDTH         : integer := 4;
   constant ITEM_COUNT           : integer := 2048 / (DATA_WIDTH/8);

   -- ------------------ Signals declaration ----------------------------------
   -- FIFO interface
   signal cu_sof_out_n      : std_logic;
   signal cu_sop_out_n      : std_logic;
   signal cu_eop_out_n      : std_logic;
   signal cu_eof_out_n      : std_logic;
   signal cu_src_rdy_out_n  : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal cu_dst_rdy_out_n  : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal cu_data_out       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal cu_rem_out        : std_logic_vector(log2(DATA_WIDTH/8)-1 
                                                                     downto 0);
   signal cu_fifo_status    : std_logic_vector
                              ((OUTPUT_COUNT*STATUS_WIDTH)-1 downto 0);
   

begin
   -- ------------------ Directly mapped signals ------------------------------
   FLS_CU_I : entity work.FLS_CU
      generic map(
         DATA_WIDTH     => DATA_WIDTH,
         OUTPUT_COUNT   => OUTPUT_COUNT,
         STATUS_WIDTH   => STATUS_WIDTH
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- input interface
         SOF_IN_N       => RX_SOF_N,
         SOP_IN_N       => RX_SOP_N,
         EOP_IN_N       => RX_EOP_N,
         EOF_IN_N       => RX_EOF_N,
         SRC_RDY_IN_N   => RX_SRC_RDY_N,
         DST_RDY_IN_N   => RX_DST_RDY_N,
         DATA_IN        => RX_DATA,
         REM_IN         => RX_REM,
         -- FIFO interface
         SOF_OUT_N      => cu_sof_out_n,
         SOP_OUT_N      => cu_sop_out_n,
         EOP_OUT_N      => cu_eop_out_n,
         EOF_OUT_N      => cu_eof_out_n,
         SRC_RDY_OUT_N  => cu_src_rdy_out_n,
         DST_RDY_OUT_N  => cu_dst_rdy_out_n,
         DATA_OUT       => cu_data_out,
         REM_OUT        => cu_rem_out,
         FIFO_STATUS    => cu_fifo_status
      );


   -- generate FrameLink FIFOs ------------------------------------------------
   GEN_FIFO: for i in 0 to OUTPUT_COUNT-1 generate

      FL_FIFO_I : entity work.FL_FIFO
         generic map(
            DATA_WIDTH     => DATA_WIDTH,
            USE_BRAMS      => true,
            ITEMS          => ITEM_COUNT,
            BLOCK_SIZE     => 1,
            STATUS_WIDTH   => STATUS_WIDTH,
            PARTS          => FRAME_PARTS
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- write interface
            RX_DATA        => cu_data_out,
            RX_REM         => cu_rem_out,
            RX_SRC_RDY_N   => cu_src_rdy_out_n(i),
            RX_DST_RDY_N   => cu_dst_rdy_out_n(i),
            RX_SOP_N       => cu_sop_out_n,
            RX_EOP_N       => cu_eop_out_n,
            RX_SOF_N       => cu_sof_out_n,
            RX_EOF_N       => cu_eof_out_n,
            -- read interface
            TX_DATA        => 
               TX_DATA(((i+1)*DATA_WIDTH)-1 downto i*DATA_WIDTH),
            TX_REM         => TX_REM
               (((i+1)*log2(DATA_WIDTH/8))-1 downto i*log2(DATA_WIDTH/8)),
            TX_SRC_RDY_N   => TX_SRC_RDY_N(i),
            TX_DST_RDY_N   => TX_DST_RDY_N(i),
            TX_SOP_N       => TX_SOP_N(i),
            TX_EOP_N       => TX_EOP_N(i),
            TX_SOF_N       => TX_SOF_N(i),
            TX_EOF_N       => TX_EOF_N(i),
            -- FIFO state signals
            LSTBLK         => open,
            FULL           => open,
            EMPTY          => open,
            STATUS 
               => cu_fifo_status((i+1)*STATUS_WIDTH-1 downto i*STATUS_WIDTH)
         );
   end generate;

end architecture full;
