-- splitter_fifo2nfifo.vhd: FrameLink Splitter architecture
-- Copyright (C) 2009 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--            Jakub Olbert <xolber00@stud.fit.vutbr.cz>
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
architecture full of FL_SPLITTER_FIFO2NFIFO is

   -- ------------------ Constants declaration --------------------------------
   -- Determines count of pseudo outputs (number of fifo2nfifo inputs has to be power of 2)
   function OUTPUT_COUNT_I
      return integer is
         variable exp : integer;
   begin
      exp := log2(OUTPUT_COUNT);
      if (2**exp > OUTPUT_COUNT) then
         return 2**exp;
      else
         return OUTPUT_COUNT;
      end if;
   end function;

   constant STATUS_WIDTH         : integer := 7;
   constant ITEM_COUNT           : integer := 2048 / (RX_DATA_WIDTH/8);
   constant BLOCK_SIZE           : integer := 128;
   constant PRE_TRANSFORM_WIDTH  : integer := RX_DATA_WIDTH/OUTPUT_COUNT_I;

   -- ------------------ Signals declaration ----------------------------------
   -- FIFO interface
   signal cu_sof_out_n      : std_logic;
   signal cu_sop_out_n      : std_logic;
   signal cu_eop_out_n      : std_logic;
   signal cu_eof_out_n      : std_logic;
   signal cu_src_rdy_out_n  : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal cu_dst_rdy_out_n  : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal cu_data_out       : std_logic_vector(RX_DATA_WIDTH-1 downto 0);
   signal cu_rem_out        : std_logic_vector(log2(RX_DATA_WIDTH/8)-1
                                                                     downto 0);
   signal cu_fifo_status    : std_logic_vector
                              ((OUTPUT_COUNT*STATUS_WIDTH)-1 downto 0);

   signal fifo_rx_sof_n     : std_logic;
   signal fifo_rx_sop_n     : std_logic;
   signal fifo_rx_eop_n     : std_logic;
   signal fifo_rx_eof_n     : std_logic;
   signal fifo_rx_src_rdy_n : std_logic_vector(OUTPUT_COUNT_I-1 downto 0);
   signal fifo_rx_dst_rdy_n : std_logic_vector(OUTPUT_COUNT_I-1 downto 0);
   signal fifo_rx_data      : std_logic_vector(RX_DATA_WIDTH-1 downto 0);
   signal fifo_rx_rem       : std_logic_vector(log2(RX_DATA_WIDTH/8)-1 downto 0);
   signal fifo_status       : std_logic_vector
                            ((OUTPUT_COUNT_I*STATUS_WIDTH)-1 downto 0);
   signal fifo_tx_sof_n     : std_logic_vector(OUTPUT_COUNT_I-1 downto 0);
   signal fifo_tx_sop_n     : std_logic_vector(OUTPUT_COUNT_I-1 downto 0);
   signal fifo_tx_eop_n     : std_logic_vector(OUTPUT_COUNT_I-1 downto 0);
   signal fifo_tx_eof_n     : std_logic_vector(OUTPUT_COUNT_I-1 downto 0);
   signal fifo_tx_src_rdy_n : std_logic_vector(OUTPUT_COUNT_I-1 downto 0);
   signal fifo_tx_dst_rdy_n : std_logic_vector(OUTPUT_COUNT_I-1 downto 0);
   signal fifo_tx_data      : std_logic_vector
                            (OUTPUT_COUNT_I*PRE_TRANSFORM_WIDTH-1 downto 0);
   signal fifo_tx_rem       : std_logic_vector
                            (OUTPUT_COUNT_I*log2(PRE_TRANSFORM_WIDTH/8)-1 downto 0);

   signal trans_sof_n       : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal trans_sop_n       : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal trans_eop_n       : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal trans_eof_n       : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal trans_src_rdy_n   : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal trans_dst_rdy_n   : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal trans_data        : std_logic_vector(OUTPUT_COUNT*TX_DATA_WIDTH-1
                                                                     downto 0);
   signal trans_rem         : std_logic_vector(OUTPUT_COUNT*log2(TX_DATA_WIDTH/8)-1
                                                                     downto 0);


begin

-- Only one output interface --------------------------------------------------
   one_output_interface : if OUTPUT_COUNT = 1 generate
      TX_DATA         <= RX_DATA;
      TX_REM          <= RX_REM;
      TX_SOF_N(0)     <= RX_SOF_N;
      TX_SOP_N(0)     <= RX_SOP_N;
      TX_EOP_N(0)     <= RX_EOP_N;
      TX_EOF_N(0)     <= RX_EOF_N;
      TX_SRC_RDY_N(0) <= RX_SRC_RDY_N;
      RX_DST_RDY_N    <= TX_DST_RDY_N(0);
   end generate one_output_interface;

-- Two or more output interfaces ----------------------------------------------
   more_output_interfaces : if OUTPUT_COUNT > 1 generate

   -- ------------------ Directly mapped signals ------------------------------
   FLS_CU_I : entity work.FLS_CU
      generic map(
         DATA_WIDTH     => RX_DATA_WIDTH,
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


   fifo_rx_sof_n        <= cu_sof_out_n;
   fifo_rx_sop_n        <= cu_sop_out_n;
   fifo_rx_eop_n        <= cu_eop_out_n;
   fifo_rx_eof_n        <= cu_eof_out_n;
   fifo_rx_data         <= cu_data_out;
   fifo_rx_rem          <= cu_rem_out;

   fifo_sig_connect_gen: for i in 0 to OUTPUT_COUNT-1 generate
      fifo_rx_src_rdy_n(i) <= cu_src_rdy_out_n(i);
      cu_dst_rdy_out_n(i)  <= fifo_rx_dst_rdy_n(i);
      cu_fifo_status((i+1)*STATUS_WIDTH-1 downto i*STATUS_WIDTH) <=
            fifo_status((i+1)*STATUS_WIDTH-1 downto i*STATUS_WIDTH);
   end generate;

   fifo_sig_const_gen: if OUTPUT_COUNT /= OUTPUT_COUNT_I generate
      fifo_const_gen: for i in OUTPUT_COUNT to OUTPUT_COUNT_I-1 generate
         fifo_rx_src_rdy_n(i) <= '1';
      end generate;
   end generate;


   -- use fifo2nfifo_buffer ---------------------------------------------------
   FIFO_2N_FIFO_BUFFER : entity work.FIFO2NFIFO_BUFFER
      generic map(
         DATA_WIDTH   => RX_DATA_WIDTH,
         OUTPUT_COUNT => OUTPUT_COUNT_I,
         BLOCK_SIZE   => BLOCK_SIZE,
         STATUS_WIDTH => STATUS_WIDTH,
         FRAME_PARTS  => FRAME_PARTS,
         USE_BRAMS    => true,
         GLOB_STATE   => false
      )
      port map(
         -- common interface
         CLK          => CLK,
         RESET        => RESET,

         -- Input interface (framelink)
         RX_SOF_N     => fifo_rx_sof_n,
         RX_SOP_N     => fifo_rx_sop_n,
         RX_EOF_N     => fifo_rx_eof_n,
         RX_EOP_N     => fifo_rx_eop_n,
         RX_SRC_RDY_N => fifo_rx_src_rdy_n,
         RX_DST_RDY_N => fifo_rx_dst_rdy_n,
         RX_DATA      => fifo_rx_data,
         RX_REM       => fifo_rx_rem,

         -- Output interface (framelink * OUTPUT_COUNT)
         TX_SOF_N     => fifo_tx_sof_n,
         TX_SOP_N     => fifo_tx_sop_n,
         TX_EOF_N     => fifo_tx_eof_n,
         TX_EOP_N     => fifo_tx_eop_n,
         TX_SRC_RDY_N => fifo_tx_src_rdy_n,
         TX_DST_RDY_N => fifo_tx_dst_rdy_n,
         TX_DATA      => fifo_tx_data,
         TX_REM       => fifo_tx_rem,

         -- fifo2nfifo status
         STATUS  => fifo_status
      );

      transform_i_gen: for i in 0 to OUTPUT_COUNT-1 generate
         fltrai: entity work.FL_TRANSFORMER
            generic map (
               RX_DATA_WIDTH  => PRE_TRANSFORM_WIDTH,
               TX_DATA_WIDTH  => TX_DATA_WIDTH
            )
            port map (
               CLK            => CLK,
               RESET          => RESET,

               -- RX interface
               RX_DATA        => fifo_tx_data((i+1)*PRE_TRANSFORM_WIDTH-1 downto
                                                            i*PRE_TRANSFORM_WIDTH),
               RX_REM         => fifo_tx_rem((i+1)*log2(PRE_TRANSFORM_WIDTH/8)-1 downto
                                                            i*log2(PRE_TRANSFORM_WIDTH/8)),
               RX_SOF_N       => fifo_tx_sof_n(i),
               RX_EOF_N       => fifo_tx_eof_n(i),
               RX_SOP_N       => fifo_tx_sop_n(i),
               RX_EOP_N       => fifo_tx_eop_n(i),
               RX_SRC_RDY_N   => fifo_tx_src_rdy_n(i),
               RX_DST_RDY_N   => fifo_tx_dst_rdy_n(i),

               -- TX interface
               TX_DATA        => trans_data((i+1)*TX_DATA_WIDTH-1 downto
                                                            i*TX_DATA_WIDTH),
               TX_REM         => trans_rem((i+1)*log2(TX_DATA_WIDTH/8)-1 downto
                                                            i*log2(TX_DATA_WIDTH/8)),
               TX_SOF_N       => trans_sof_n(i),
               TX_EOF_N       => trans_eof_n(i),
               TX_SOP_N       => trans_sop_n(i),
               TX_EOP_N       => trans_eop_n(i),
               TX_SRC_RDY_N   => trans_src_rdy_n(i),
               TX_DST_RDY_N   => trans_dst_rdy_n(i)
            );
      end generate;

      TX_DATA         <= trans_data;
      TX_REM          <= trans_rem;
      TX_SOF_N        <= trans_sof_n;
      TX_SOP_N        <= trans_sop_n;
      TX_EOP_N        <= trans_eop_n;
      TX_EOF_N        <= trans_eof_n;
      TX_SRC_RDY_N    <= trans_src_rdy_n;
      trans_dst_rdy_n <= TX_DST_RDY_N;

   end generate more_output_interfaces;

end architecture full;

