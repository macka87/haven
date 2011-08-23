-- ticket_sequencer.vhd: Ticket Sequencer architecture
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--            Libor Polčák <polcak_l@liberouter.org>
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

use work.fifo_pkg.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_TICKET_SEQUENCER is

   -- ------------------ Constants declaration --------------------------------
   -- Determines count of pseudo inputs (number of inputs has to be power of 2)
   function INPUT_COUNT_I
      return integer is
         variable exp : integer;
   begin
      exp := log2(INPUT_COUNT);
      if (2**exp > INPUT_COUNT) then
         return 2**exp;
      else
         return INPUT_COUNT;
      end if;
   end function;

   constant STATUS_WIDTH         : integer := 4;
   constant CHANNEL_WIDTH        : integer := INPUT_WIDTH + INPUT_WIDTH/8;
   constant NFIFO2FIFO_WIDTH     : integer := CHANNEL_WIDTH * INPUT_COUNT_I;
   constant MEM_DATA_WIDTH       : integer := INPUT_WIDTH * INPUT_COUNT_I;
   constant BRAM_SIZE            : integer := 2048;
   constant BRAM_BLOCK_SIZE      : integer := BRAM_SIZE / (MEM_DATA_WIDTH/8);
   
   function BLOCK_SIZE
      return integer is
   begin
      if (LUT_MEMORY = true) then return LUT_BLOCK_SIZE;
      else return BRAM_BLOCK_SIZE;
      end if;
   end function;

   function OUTPUT_REG
      return boolean is
   begin
      if (LUT_MEMORY = true) then return true;
      else return false;
      end if;
   end function;
   
   -- set to cover situation, when memory is full of one-word frames
   constant FRAMECOUNTER_WIDTH   : integer := log2(BLOCK_SIZE+1);

   -- Ticket part
   signal tick_fifo_tx_dst_rdy : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal tick_fifo_tx_src_rdy : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal ticket_waiting       : std_logic_vector(INPUT_COUNT*TICKET_WIDTH-1
                                                                  downto 0);
   -- NFIFO2FIFO interface
   signal nfifo2fifo_data_in     : std_logic_vector(NFIFO2FIFO_WIDTH-1 downto 0);
   signal nfifo2fifo_write       : std_logic_vector(INPUT_COUNT_I-1 downto 0);
   signal nfifo2fifo_full        : std_logic_vector(INPUT_COUNT_I-1 downto 0);

   signal nfifo2fifo_data_out    : std_logic_vector(NFIFO2FIFO_WIDTH-1 downto 0);
   signal nfifo2fifo_data_vld    : std_logic;
   signal nfifo2fifo_block_addr  : std_logic_vector(abs(log2(INPUT_COUNT_I)-1) downto 0);
   signal nfifo2fifo_read        : std_logic;
   signal nfifo2fifo_empty       : std_logic_vector(INPUT_COUNT_I-1 downto 0);
   signal nfifo2fifo_status      : std_logic_vector(log2(BLOCK_SIZE+1)*INPUT_COUNT_I-1 downto 0);

   -- Output block input interface signals
   signal out_rx_sof_n         : std_logic;
   signal out_rx_sop_n         : std_logic;
   signal out_rx_eop_n         : std_logic;
   signal out_rx_eof_n         : std_logic;
   signal out_rx_src_rdy_n     : std_logic;
   signal out_rx_dst_rdy_n     : std_logic;
   signal out_rx_data          : std_logic_vector(OUTPUT_WIDTH-1 downto 0);
   signal out_rx_rem           : std_logic_vector(log2(OUTPUT_WIDTH/8)-1 
                                downto 0);
   signal out_tx_sof_n         : std_logic;
   signal out_tx_sop_n         : std_logic;
   signal out_tx_eop_n         : std_logic;
   signal out_tx_eof_n         : std_logic;
   signal out_tx_src_rdy_n     : std_logic;
   signal out_tx_dst_rdy_n     : std_logic;
   signal out_tx_data          : std_logic_vector(OUTPUT_WIDTH-1 downto 0);
   signal out_tx_rem           : std_logic_vector(log2(OUTPUT_WIDTH/8)-1 
                                downto 0);

   -- FSM Input control unit signals
   signal comparator         : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fsm_src_rdy_out_n  : std_logic;

   -- - FSM connection signals
   signal ticket_rdy         : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal actual_ticket      : std_logic_vector(TICKET_WIDTH-1 downto 0);
   signal ticket_exchange    : std_logic;
   signal input_active       : std_logic_vector(INPUT_COUNT-1 downto 0);

   signal out_ifc             : std_logic_vector(log2(INPUT_COUNT_I)-1 downto 0);

begin

   -- -------------------------------------------------------------------------
   --                         TICKET PART
   -- -------------------------------------------------------------------------

   -- Ticket FIFOs
   tick_fifo_gen: for i in 0 to INPUT_COUNT - 1 generate
      ticket_fifosi: entity work.FIFO_SYNC_ORD
         generic map (
            mem_type       => TICKET_FIFO_TYPE,
            latency        => 1,
            items          => TICKET_FIFO_ITEMS,
            item_width     => TICKET_WIDTH,
            prefetch       => true
         )
         port map (
            CLK            => CLK,
            RESET          => RESET,

            WR             => TICKET_WR(i),
            DI             => TICKET((i+1)*TICKET_WIDTH-1 downto
                                                          i*TICKET_WIDTH),

            RD             => tick_fifo_tx_dst_rdy(i),
            DO             => ticket_waiting((i+1)*TICKET_WIDTH-1 downto
                                                          i*TICKET_WIDTH),
            DO_DV          => tick_fifo_tx_src_rdy(i),

            FULL           => TICKET_FULL(i),
            EMPTY          => open,
            STATUS         => open
         );
   end generate tick_fifo_gen;



   -- -------------------------------------------------------------------------
   --                      INPUT DATA TRANSFORMATION
   -- -------------------------------------------------------------------------
   -- generate frame aligner for every input interface
   GEN_ALIGN_FRAME : for i in 0 to INPUT_COUNT-1 generate
      ALIGN_FRAME_I : entity work.FLB_ALIGN_FRAME
         generic map(
            INPUT_WIDTH    => INPUT_WIDTH,
            INPUT_COUNT    => INPUT_COUNT,
            FRAME_PARTS    => PARTS
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- input interface
            RX_SOF_N       => RX_SOF_N(i),
            RX_SOP_N       => RX_SOP_N(i),
            RX_EOP_N       => RX_EOP_N(i),
            RX_EOF_N       => RX_EOF_N(i),
            RX_SRC_RDY_N   => RX_SRC_RDY_N(i),
            RX_DST_RDY_N   => RX_DST_RDY_N(i),
            RX_DATA        => RX_DATA((i+1)*INPUT_WIDTH-1 downto i*INPUT_WIDTH),
            RX_REM         => RX_REM((i+1)*log2(INPUT_WIDTH/8)-1 downto i*log2(INPUT_WIDTH/8)),
            -- output interface
            DATA_OUT       => nfifo2fifo_data_in((i+1)*CHANNEL_WIDTH-1 downto i*CHANNEL_WIDTH),
            WRITE          => nfifo2fifo_write(i),
            FULL           => nfifo2fifo_full(i),
            -- other
            NEW_FRAME      => open,
            FRAME_PART     => open
         );
   end generate;

   nfifo2fifo_write_gen_if: if INPUT_COUNT_I /= INPUT_COUNT generate
      nfifo2fifo_write_gen: for i in INPUT_COUNT to INPUT_COUNT_I-1 generate
         nfifo2fifo_write(i) <= '0';
      end generate;
   end generate;

   -- -------------------------------------------------------------------------
   --                              NFIFO2FIFO
   -- -------------------------------------------------------------------------
   NFIFO2FIFO_I : entity work.NFIFO2FIFO
   generic map(
      DATA_WIDTH => NFIFO2FIFO_WIDTH,
      FLOWS      => INPUT_COUNT_I,
      BLOCK_SIZE => BLOCK_SIZE,
      LUT_MEMORY => LUT_MEMORY,
      OUTPUT_REG => OUTPUT_REG,
      GLOB_STATE => false
   )
   port map(
      CLK        => CLK,
      RESET      => RESET,
      -- Write interface
      DATA_IN    => nfifo2fifo_data_in,
      WRITE      => nfifo2fifo_write,
      FULL       => nfifo2fifo_full,
      -- Read interface
      DATA_OUT   => nfifo2fifo_data_out,
      DATA_VLD   => nfifo2fifo_data_vld,
      BLOCK_ADDR => nfifo2fifo_block_addr,
      READ       => nfifo2fifo_read,
      PIPE_EN    => nfifo2fifo_read,
      EMPTY      => nfifo2fifo_empty,
      STATUS     => nfifo2fifo_status
   );

   DATA_TRANSFORMER_I : entity work.FLB_DATA_TRANSFORMER
      generic map(
         INPUT_WIDTH    => INPUT_WIDTH,
         INPUT_COUNT    => INPUT_COUNT_I,
         OUTPUT_WIDTH   => OUTPUT_WIDTH,
         STATUS_WIDTH   => STATUS_WIDTH,
         BLOCK_SIZE     => BLOCK_SIZE,
         FRAME_PARTS    => PARTS
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- NFIFO2FIFO interface
         DATA_OUT       => nfifo2fifo_data_out,
         DATA_VLD       => nfifo2fifo_data_vld,
         BLOCK_ADDR     => nfifo2fifo_block_addr,
         READ           => nfifo2fifo_read,
         EMPTY          => nfifo2fifo_empty,
         STATUS         => nfifo2fifo_status,
         -- Output data
         TX_SOF_N       => out_rx_sof_n,
         TX_SOP_N       => out_rx_sop_n,
         TX_EOP_N       => out_rx_eop_n,
         TX_EOF_N       => out_rx_eof_n,
         TX_SRC_RDY_N   => out_rx_src_rdy_n,
         TX_DST_RDY_N   => out_rx_dst_rdy_n,
         TX_DATA        => out_rx_data,
         TX_REM         => out_rx_rem,
         -- Output block interface
         TX_STATUS      => open,
         TX_EMPTY       => open,
         TX_IFC         => out_ifc,
         -- Other
         FRAME_DONE     => open
      );

   -- -------------------------------------------------------------------------
   --                              OUTPUT PART
   -- -------------------------------------------------------------------------


   fsmi: entity work.FL_SEQUENCER_FSM
      generic map (
         INPUT_COUNT       => INPUT_COUNT,
         TICKET_WIDTH      => TICKET_WIDTH
      )
      port map (
         CLK               => CLK,
         RESET             => RESET,
         -- FSM input signals
         TICKET_RDY        => ticket_rdy,
         FL_EOF_N          => out_rx_eof_n,
         OUTPUT_RDY_N      => out_rx_dst_rdy_n,
         SRC_RDY_IN_N      => out_rx_src_rdy_n,
         -- FSM output signals
         MX_SEL            => out_ifc,
         TICKET_NUMBER     => actual_ticket,
         TICKET_EXCHANGE   => ticket_exchange,
         INPUT_ACTIVE      => input_active,
         SRC_RDY_OUT_N     => fsm_src_rdy_out_n
      );

   -----------------------------------------------------------------------------
   -- Input control unit
   --flfii_tx_dst_rdyg: for i in 0 to INPUT_COUNT-1 generate
   --   out_rx_dst_rdy_n <= (not input_active(i)) or out_tx_dst_rdy_n;
   --end generate;
   out_rx_dst_rdy_np: process(input_active, out_tx_dst_rdy_n)
   begin
      if input_active /= conv_std_logic_vector(0, input_active'length) then
         out_rx_dst_rdy_n <= out_tx_dst_rdy_n;
      else
         out_rx_dst_rdy_n <= '1';
      end if;
   end process;

   tick_fifo_tx_dst_rdyg: for i in 0 to INPUT_COUNT-1 generate
      tick_fifo_tx_dst_rdy(i) <= input_active(i) and ticket_exchange;
   end generate;

   ticket_rdyg: for i in 0 to INPUT_COUNT-1 generate
      ticket_rdy(i) <= tick_fifo_tx_src_rdy(i) and comparator(i);
   end generate;

   comparatorg: for i in 0 to INPUT_COUNT-1 generate
      process(ticket_waiting((i+1)*TICKET_WIDTH-1 downto i*TICKET_WIDTH),
                                                                actual_ticket)
      begin
         if (ticket_waiting((i+1)*TICKET_WIDTH-1 downto i*TICKET_WIDTH)
                                                         = actual_ticket) then
            comparator(i) <= '1';
         else
            comparator(i) <= '0';
         end if;
      end process;
   end generate;

   out_tx_sof_n <= out_rx_sof_n;
   out_tx_eop_n <= out_rx_eop_n;
   out_tx_sop_n <= out_rx_sop_n;
   out_tx_eof_n <= out_rx_eof_n;
   out_tx_src_rdy_n <= out_rx_src_rdy_n or fsm_src_rdy_out_n;
   out_tx_data <= out_rx_data;
   out_tx_rem <= out_rx_rem;

   -- generate FrameLink pipe to achieve better timing
--   GEN_PIPE: if (INPUT_WIDTH*INPUT_COUNT_I = OUTPUT_WIDTH) generate
      OUTPUT_PIPE : entity work.FL_PIPE
         generic map(
            -- FrameLink Data Width
            DATA_WIDTH     => OUTPUT_WIDTH,
            USE_OUTREG     => false
         )
         port map(
            -- Common interface 
            CLK            => CLK,
            RESET          => RESET,
            -- Input interface
            RX_SOF_N       => out_tx_sof_n,
            RX_SOP_N       => out_tx_sop_n,
            RX_EOP_N       => out_tx_eop_n,
            RX_EOF_N       => out_tx_eof_n,
            RX_SRC_RDY_N   => out_tx_src_rdy_n,
            RX_DST_RDY_N   => out_tx_dst_rdy_n,
            RX_DATA        => out_tx_data,
            RX_REM         => out_tx_rem,

            -- Output interface
            TX_SOF_N       => TX_SOF_N,
            TX_EOP_N       => TX_EOP_N,
            TX_SOP_N       => TX_SOP_N,
            TX_EOF_N       => TX_EOF_N,
            TX_SRC_RDY_N   => TX_SRC_RDY_N,
            TX_DST_RDY_N   => TX_DST_RDY_N,
            TX_DATA        => TX_DATA,
            TX_REM         => TX_REM
         );
 --  end generate;

 --  GEN_NOPIPE: if (INPUT_WIDTH*INPUT_COUNT_I /= OUTPUT_WIDTH) generate
 --     TX_SOF_N       <= out_tx_sof_n;
 --     TX_EOP_N       <= out_tx_eop_n;
 --     TX_SOP_N       <= out_tx_sop_n;
 --     TX_EOF_N       <= out_tx_eof_n;
 --     TX_SRC_RDY_N   <= out_tx_src_rdy_n;
 --     out_tx_dst_rdy_n   <= TX_DST_RDY_N;
 --     TX_DATA        <= out_tx_data;
 --     TX_REM         <= out_tx_rem;
 --  end generate;
end architecture full;
