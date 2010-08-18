-- sequencer.vhd: Frame Link protocol Sequencer architecture
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
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
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;
use work.fifo_pkg.all;


-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------

architecture FL_SEQUENCER_ARCH of FL_SEQUENCER is
   -- - Constants declaration

   -- - FL Cutter output data
   signal ticket : std_logic_vector(INPUT_COUNT*TICKET_SIZE*8-1 downto 0);
   signal ticket_valid : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal flcut_tx_data : std_logic_vector(INPUT_COUNT*INPUT_WIDTH-1 downto 0);
   signal flcut_tx_rem : std_logic_vector(INPUT_COUNT*log2(INPUT_WIDTH/8)-1
                                                                  downto 0);
   signal flcut_tx_src_rdy_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal flcut_tx_dst_rdy_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal flcut_tx_sop_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal flcut_tx_eop_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal flcut_tx_sof_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal flcut_tx_eof_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   
   -- Ondra Lengal:
   -- - register for detection of rising edge of cutter ticket valid:
   --   stores the previous value of signal "ticket_valid"
   signal reg_ticket_valid_prev : std_logic_vector(INPUT_COUNT-1 downto 0);

   -- - FL Transformer input signals
   signal fltra_rx_data  : std_logic_vector(INPUT_COUNT*INPUT_WIDTH-1 downto 0);
   signal fltra_rx_rem   : std_logic_vector(INPUT_COUNT*log2(INPUT_WIDTH/8)-1
                                                                  downto 0);
   signal fltra_rx_src_rdy_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fltra_rx_dst_rdy_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fltra_rx_sop_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fltra_rx_eop_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fltra_rx_sof_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fltra_rx_eof_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   -- - FL Transformer output data
   signal fltra_tx_data  : std_logic_vector(INPUT_COUNT*OUTPUT_WIDTH-1 downto 0);
   signal fltra_tx_rem   : std_logic_vector(INPUT_COUNT*log2(OUTPUT_WIDTH/8)-1
                                                                  downto 0);
   signal fltra_tx_src_rdy_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fltra_tx_dst_rdy_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fltra_tx_sop_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fltra_tx_eop_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fltra_tx_sof_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fltra_tx_eof_n : std_logic_vector(INPUT_COUNT-1 downto 0);

   -- - FL FIFO (input) output signals
   signal flfii_tx_data : std_logic_vector(INPUT_COUNT*OUTPUT_WIDTH-1 downto 0);
   signal flfii_tx_rem : std_logic_vector(INPUT_COUNT*log2(OUTPUT_WIDTH/8)-1
                                                                  downto 0);
   signal flfii_tx_src_rdy_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal flfii_tx_dst_rdy_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal flfii_tx_sop_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal flfii_tx_eop_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal flfii_tx_sof_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal flfii_tx_eof_n : std_logic_vector(INPUT_COUNT-1 downto 0);

   -- - Ticket FIFO signals
   signal tick_fifo_rx_src_rdy : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal tick_fifo_full       : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal tick_fifo_tx_dst_rdy : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal tick_fifo_tx_src_rdy : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal ticket_waiting       : std_logic_vector(INPUT_COUNT*TICKET_SIZE*8-1
                                                                  downto 0);
   -- Registers before Ticket FIFO to reduce path length
   signal reg_tick_fifo_rx_src_rdy : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal reg_tick_fifo_rx_src_rdy_we : std_logic_vector(INPUT_COUNT-1
                                                                    downto 0);
   signal reg_ticket           : std_logic_vector(INPUT_COUNT*TICKET_SIZE*8-1
                                                                  downto 0);
   signal reg_ticket_we        : std_logic_vector(INPUT_COUNT-1 downto 0);

   -- - Multiplexers signal
   signal mx_sel             : std_logic_vector(log2(INPUT_COUNT)-1 downto 0);

   -- - FrameLink protocol between multiplexers and output part signals
   signal flmx_tx_data       : std_logic_vector(OUTPUT_WIDTH-1 downto 0);
   signal flmx_tx_rem        : std_logic_vector(log2(OUTPUT_WIDTH/8)-1 downto 0);
   signal flmx_tx_sop_n      : std_logic_vector(0 downto 0);
   signal flmx_tx_eop_n      : std_logic_vector(0 downto 0);
   signal flmx_tx_sof_n      : std_logic_vector(0 downto 0);
   signal flmx_tx_eof_n      : std_logic_vector(0 downto 0);

   -- - FSM connection signals
   signal ticket_rdy         : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal actual_ticket      : std_logic_vector(TICKET_SIZE*8-1 downto 0);
   signal ticket_exchange    : std_logic;
   signal input_active       : std_logic_vector(INPUT_COUNT-1 downto 0);

   -- FSM Input control unit signals
   signal comparator         : std_logic_vector(INPUT_COUNT-1 downto 0);

   -- - FSM signals
   signal fsm_src_rdy_in_n   : std_logic_vector(0 downto 0);
   signal fsm_src_rdy_out_n  : std_logic;

   -- - FL output part RX signals
   signal flout_rx_data    : std_logic_vector(OUTPUT_WIDTH-1 downto 0);
   signal flout_rx_rem     : std_logic_vector(log2(OUTPUT_WIDTH/8)-1 downto 0);
   signal flout_rx_src_rdy_n : std_logic;
   signal flout_rx_dst_rdy_n : std_logic;
   signal flout_rx_sop_n     : std_logic;
   signal flout_rx_eop_n     : std_logic;
   signal flout_rx_sof_n     : std_logic;
   signal flout_rx_eof_n     : std_logic;


begin
   -----------------------------------------------------------------------------
   -- Input part
   -----------------------------------------------------------------------------

   -- FrameLink Cutter
   fl_cutter_gen: for i in 0 to INPUT_COUNT - 1 generate
      fl_cutter: entity work.FL_CUTTER_FAKE
         generic map (
            DATA_WIDTH        => INPUT_WIDTH,
            PART              => TICKET_PART,
            OFFSET            => TICKET_OFFSET,
            SIZE              => TICKET_SIZE
         )
         port map (
            CLK               => CLK,
            RESET             => RESET,
            -- Tickets
            CUTTED_DATA       => ticket((i+1)*TICKET_SIZE*8-1 downto
                                                      i*TICKET_SIZE*8),
            CUTTED_VLD        => ticket_valid(i),
            -- Input
            RX_DATA           => RX_DATA((i+1)*INPUT_WIDTH-1 downto
                                                      i*INPUT_WIDTH),
            RX_REM            => RX_REM((i+1)*log2(INPUT_WIDTH/8)-1 downto
                                                      i*log2(INPUT_WIDTH/8)),
            RX_SRC_RDY_N      => RX_SRC_RDY_N(i),
            RX_DST_RDY_N      => RX_DST_RDY_N(i),
            RX_SOP_N          => RX_SOP_N(i),
            RX_EOP_N          => RX_EOP_N(i),
            RX_SOF_N          => RX_SOF_N(i),
            RX_EOF_N          => RX_EOF_N(i),
            -- Output
            TX_DATA           => flcut_tx_data((i+1)*INPUT_WIDTH-1 downto
                                                      i*INPUT_WIDTH),
            TX_REM            => flcut_tx_rem((i+1)*log2(INPUT_WIDTH/8)-1 downto
                                                      i*log2(INPUT_WIDTH/8)),
            TX_SRC_RDY_N      => flcut_tx_src_rdy_n(i),
            TX_DST_RDY_N      => flcut_tx_dst_rdy_n(i),
            TX_SOP_N          => flcut_tx_sop_n(i),
            TX_EOP_N          => flcut_tx_eop_n(i),
            TX_SOF_N          => flcut_tx_sof_n(i),
            TX_EOF_N          => flcut_tx_eof_n(i)
         );
   end generate;

   -- Control of DST RDY signal for FrameLink Cutter
   flcut_tx_dst_rdy_n <= fltra_rx_dst_rdy_n or tick_fifo_full;

   -- Control of SRC RDY signal for FrameLink Cutter
   fltra_rx_src_rdy_n <= tick_fifo_full or flcut_tx_src_rdy_n;

   fltra_rx_data        <= flcut_tx_data;
   fltra_rx_rem         <= flcut_tx_rem;
   fltra_rx_sop_n       <= flcut_tx_sop_n;
   fltra_rx_eop_n       <= flcut_tx_eop_n;
   fltra_rx_sof_n       <= flcut_tx_sof_n;
   fltra_rx_eof_n       <= flcut_tx_eof_n;
           
   ----------------------------------------------------------------------------
   -- Ticket FIFOs
   ----------------------------------------------------------------------------

   -- Ondra Lengal:
   -- Register used for detection of rising edge of 'ticket_valid' signal
   reg_ticket_valid_prevp: process(CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            reg_ticket_valid_prev <= (others => '0');
         else
            reg_ticket_valid_prev <= ticket_valid;
         end if;
      end if;
   end process;

   -- Ticket FIFOs control signals
   --tick_fifo_rx_src_rdy <= ticket_valid and (not (fltra_rx_dst_rdy_n));
      -- Ondra Lengal: changed in order to capture _all_ tickets from the cutter
   tick_fifo_rx_src_rdy <= ticket_valid and (not reg_ticket_valid_prev);

   -- Registers in front of TicketFIFOs to reduce path length -----------------
   reg_tick_fifo_rx_src_rdy_we <= not tick_fifo_full;
   reg_ticket_we <= not tick_fifo_full;

   -- register reg_tick_fifo_rx_src_rdy ---------------------------------------
   reg_tick_fifo_rx_src_rdygen: for i in 0 to INPUT_COUNT - 1 generate
      reg_tick_fifo_rx_src_rdyp: process(RESET, CLK)
      begin
         if (RESET = '1') then
            reg_tick_fifo_rx_src_rdy(i) <= '0';
         elsif (CLK'event AND CLK = '1') then
            if (reg_tick_fifo_rx_src_rdy_we(i) = '1') then
               reg_tick_fifo_rx_src_rdy(i) <= tick_fifo_rx_src_rdy(i);
            end if;
         end if;
      end process;
   end generate reg_tick_fifo_rx_src_rdygen;

   -- register reg_ticket -----------------------------------------------------
   reg_ticket_gen: for i in 0 to INPUT_COUNT - 1 generate
      reg_ticketp: process(RESET, CLK)
      begin
         if (RESET = '1') then
            reg_ticket((i+1)*TICKET_SIZE*8-1 downto i*TICKET_SIZE*8) <=
                                                             (others => '0');
         elsif (CLK'event AND CLK = '1') then
            if (reg_ticket_we(i) = '1') then
               reg_ticket((i+1)*TICKET_SIZE*8-1 downto i*TICKET_SIZE*8) <= 
                        ticket((i+1)*TICKET_SIZE*8-1 downto i*TICKET_SIZE*8);
            end if;
         end if;
      end process;
   end generate reg_ticket_gen;

   -----------------------------------------------------------------------------
   -- Ticket Sequencer
   -----------------------------------------------------------------------------

   ticket_sequencer_i: entity work.FL_TICKET_SEQUENCER
      generic map (
         -- Data width of one input interface (16, 32, 64, 128 bits)
         INPUT_WIDTH          => INPUT_WIDTH,
         -- Number of input interfaces
         INPUT_COUNT          => INPUT_COUNT,
         -- Output width (bits)
         OUTPUT_WIDTH         => OUTPUT_WIDTH,
         -- Header / Footer data present
         PARTS                => PARTS,
         -- Size of the ticket (in bits)
         TICKET_WIDTH         => TICKET_SIZE*8,
         -- Number of items in input ticket FIFOs
         -- TICKET_WIDTH wide
         TICKET_FIFO_ITEMS    => TICKET_FIFO_ITEMS,
         -- Type of memory used for ticket FIFOs
         TICKET_FIFO_TYPE     => LUT,
         -- Generic from Binder fifo 2 nfifo with no description
         LUT_MEMORY           => true,
         -- Generic from Binder fifo 2 nfifo with no description
         LUT_BLOCK_SIZE       => 512
      )
      port map (
         -- Common signals
         -- clock sigal
         CLK               => CLK,
         -- asynchronous reset, active in '1'
         RESET             => RESET,

         -- input FrameLink interface
         RX_SOF_N       => fltra_rx_sof_n,
         RX_SOP_N       => fltra_rx_sop_n,
         RX_EOP_N       => fltra_rx_eop_n,
         RX_EOF_N       => fltra_rx_eof_n,
         RX_SRC_RDY_N   => fltra_rx_src_rdy_n,
         RX_DST_RDY_N   => fltra_rx_dst_rdy_n,
         RX_DATA        => fltra_rx_data,
         RX_REM         => fltra_rx_rem,

         TICKET         => reg_ticket,
         TICKET_WR      => reg_tick_fifo_rx_src_rdy,
         TICKET_FULL    => tick_fifo_full,

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

end architecture FL_SEQUENCER_ARCH;
