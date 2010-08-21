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

use work.fifo_pkg.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_TICKET_SPLITTER_FIFO2NFIFO is

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

   constant STATUS_WIDTH         : integer := 4;
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

   signal fifo_sof_rx_n       : std_logic;
   signal fifo_sop_rx_n       : std_logic;
   signal fifo_eop_rx_n       : std_logic;
   signal fifo_eof_rx_n       : std_logic;
   signal fifo_src_rdy_rx_n   : std_logic_vector(OUTPUT_COUNT_I-1 downto 0);
   signal fifo_dst_rdy_rx_n   : std_logic_vector(OUTPUT_COUNT_I-1 downto 0);
   signal fifo_data_rx        : std_logic_vector(RX_DATA_WIDTH-1 downto 0);
   signal fifo_rem_rx         : std_logic_vector(log2(RX_DATA_WIDTH/8)-1 downto 0);
   signal fifo_status         : std_logic_vector
                              ((OUTPUT_COUNT_I*STATUS_WIDTH)-1 downto 0);

   signal fifo_tx_sof_n       : std_logic_vector(OUTPUT_COUNT_I-1 downto 0);
   signal fifo_tx_sop_n       : std_logic_vector(OUTPUT_COUNT_I-1 downto 0);
   signal fifo_tx_eop_n       : std_logic_vector(OUTPUT_COUNT_I-1 downto 0);
   signal fifo_tx_eof_n       : std_logic_vector(OUTPUT_COUNT_I-1 downto 0);
   signal fifo_tx_src_rdy_n   : std_logic_vector(OUTPUT_COUNT_I-1 downto 0);
   signal fifo_tx_dst_rdy_n   : std_logic_vector(OUTPUT_COUNT_I-1 downto 0);
   signal fifo_tx_data        : std_logic_vector(OUTPUT_COUNT_I*PRE_TRANSFORM_WIDTH-1
                                                                           downto 0);
   signal fifo_tx_rem         : std_logic_vector(OUTPUT_COUNT_I*log2(PRE_TRANSFORM_WIDTH/8)-1
                                                                           downto 0);

   signal trans_tx_sof_n      : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal trans_tx_sop_n      : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal trans_tx_eop_n      : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal trans_tx_eof_n      : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal trans_tx_src_rdy_n  : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal trans_tx_dst_rdy_n  : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal trans_tx_data       : std_logic_vector(OUTPUT_COUNT*TX_DATA_WIDTH-1
                                                                           downto 0);
   signal trans_tx_rem        : std_logic_vector(OUTPUT_COUNT*log2(TX_DATA_WIDTH/8)-1
                                                                           downto 0);

   signal ticket_wr           : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal ticket_do           : std_logic_vector(OUTPUT_COUNT*TICKET_WIDTH-1 downto 0);
   signal ticket_do_dv        : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal ticket_full         : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal ticket_writeable_n  : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal ticket_trans_n      : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal ctrl_data_in_rq_i   : std_logic;

begin
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


   fifo_sof_rx_n        <= cu_sof_out_n;
   fifo_sop_rx_n        <= cu_sop_out_n;
   fifo_eop_rx_n        <= cu_eop_out_n;
   fifo_eof_rx_n        <= cu_eof_out_n;
   fifo_data_rx         <= cu_data_out;
   fifo_rem_rx          <= cu_rem_out;

   fifo_sig_connect_gen: for i in 0 to OUTPUT_COUNT-1 generate
      fifo_src_rdy_rx_n(i) <= cu_src_rdy_out_n(i) or (ticket_writeable_n(i) and not cu_sof_out_n);
      cu_dst_rdy_out_n(i) <= fifo_dst_rdy_rx_n(i) or (ticket_writeable_n(i) and not cu_sof_out_n);
      cu_fifo_status((i+1)*STATUS_WIDTH-1 downto i*STATUS_WIDTH) <=
            fifo_status((i+1)*STATUS_WIDTH-1 downto i*STATUS_WIDTH);
   end generate;

   fifo_sig_const_gen: if OUTPUT_COUNT /= OUTPUT_COUNT_I generate
      fifo_const_gen: for i in OUTPUT_COUNT to OUTPUT_COUNT_I-1 generate
         fifo_src_rdy_rx_n(i) <= '1';
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
         RX_SOF_N     => fifo_sof_rx_n,
         RX_SOP_N     => fifo_sop_rx_n,
         RX_EOF_N     => fifo_eof_rx_n,
         RX_EOP_N     => fifo_eop_rx_n,
         RX_SRC_RDY_N => fifo_src_rdy_rx_n,
         RX_DST_RDY_N => fifo_dst_rdy_rx_n,
         RX_DATA      => fifo_data_rx,
         RX_REM       => fifo_rem_rx,

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
               TX_DATA        => trans_tx_data((i+1)*TX_DATA_WIDTH-1 downto
                                                            i*TX_DATA_WIDTH),
               TX_REM         => trans_tx_rem((i+1)*log2(TX_DATA_WIDTH/8)-1 downto
                                                            i*log2(TX_DATA_WIDTH/8)),
               TX_SOF_N       => trans_tx_sof_n(i),
               TX_EOF_N       => trans_tx_eof_n(i),
               TX_SOP_N       => trans_tx_sop_n(i),
               TX_EOP_N       => trans_tx_eop_n(i),
               TX_SRC_RDY_N   => trans_tx_src_rdy_n(i),
               TX_DST_RDY_N   => trans_tx_dst_rdy_n(i)
            );
      end generate;

      notransform_i_gen: for i in OUTPUT_COUNT to OUTPUT_COUNT_I-1 generate
         fifo_tx_dst_rdy_n(i) <= '1';
      end generate;

      TX_DATA              <= trans_tx_data;
      TX_REM               <= trans_tx_rem;
      TX_SOF_N             <= trans_tx_sof_n;
      TX_SOP_N             <= trans_tx_sop_n;
      TX_EOP_N             <= trans_tx_eop_n;
      TX_EOF_N             <= trans_tx_eof_n;
      TX_SRC_RDY_N         <= trans_tx_src_rdy_n;
      trans_tx_dst_rdy_n   <= TX_DST_RDY_N;


   -- Ticket part (FIFOs)
   tick_fifo_gen: for i in 0 to OUTPUT_COUNT - 1 generate
      ticket_fifosi: entity work.FIFO_SYNC_ORD
         generic map (
            mem_type       => LUT,
            latency        => 1,
            items          => TICKET_FIFO_ITEMS,
            item_width     => TICKET_WIDTH,
            prefetch       => true
         )
         port map (
            CLK            => CLK,
            RESET          => RESET,

            WR             => ticket_wr(i),
            DI             => CTRL_DATA_IN,

            RD             => CTRL_DATA_OUT_RQ(i),
            DO             => ticket_do((i+1)*TICKET_WIDTH-1 downto
                                                          i*TICKET_WIDTH),
            DO_DV          => ticket_do_dv(i),

            FULL           => ticket_full(i),
            EMPTY          => open,
            STATUS         => open
         );
   end generate tick_fifo_gen;

   ticket_logic_gen: for i in 0 to OUTPUT_COUNT-1 generate
      ticket_writeable_n(i) <= ticket_full(i) or (not CTRL_DATA_IN_VLD);
      ticket_trans_n(i) <= ticket_writeable_n(i) or cu_sof_out_n;
      ticket_wr(i) <= not (fifo_dst_rdy_rx_n(i) or cu_src_rdy_out_n(i) or ticket_trans_n(i));
   end generate;

   ctrl_rq_gen_orp: process(ticket_wr)
   begin
      if (ticket_wr /= conv_std_logic_vector(0, ticket_wr'length)) then
         ctrl_data_in_rq_i <= '1';
      else
         ctrl_data_in_rq_i <= '0';
      end if;
   end process;

   -- Chipscope ready unit
   CTRL_DATA_IN_RQ   <= ctrl_data_in_rq_i;
   CTRL_DATA_OUT     <= ticket_do;
   CTRL_DATA_OUT_VLD <= ticket_do_dv;

end architecture full;

