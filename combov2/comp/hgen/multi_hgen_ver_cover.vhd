-- multi_hgen_ver_cover.vhd: Verification cover of HGEN
-- Copyright (C) 2011 Ondrej Lengal <ilengal@fit.vutbr.cz>
--
-- $Id$

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;

-- ------------------------------------------------------------------------
--                        Entity declaration
-- ------------------------------------------------------------------------
entity MULTI_HGEN_VER_COVER is
   generic(
      -- the data width of the data input/output
      DATA_WIDTH     : integer   := 128;
      BRANCH_COUNT   : integer   := 8;
      USE_BRAMS_FOR_HGEN_FIFO : boolean := true
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input data interface
      RX_DATA        :  in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         :  in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOF_N       :  in std_logic;
      RX_EOF_N       :  in std_logic;
      RX_SOP_N       :  in std_logic;
      RX_EOP_N       :  in std_logic;
      RX_SRC_RDY_N   :  in std_logic;
      RX_DST_RDY_N   : out std_logic;

      -- output data interface
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   :  in std_logic
   );

end entity;

architecture arch of MULTI_HGEN_VER_COVER is

   constant INPUT_PARTS       : integer := 1;
   constant BRANCH_PARTS      : integer := 1;
   constant TICKET_WIDTH      : integer := 12; -- bits
   constant TICKET_FIFO_ITEMS : integer := 16;

   constant HGEN_DATA_WIDTH   : integer := 128;

   -- Ticket counter
   signal cnt_ticket          : std_logic_vector(TICKET_WIDTH-1 downto 0);
   signal cnt_ticket_ce       : std_logic;
   signal cnt_ticket_vld      : std_logic;

   -- Splitter -> Sequencer ticket interface
   signal ticket              : std_logic_vector(BRANCH_COUNT*TICKET_WIDTH-1 downto 0);
   signal ticket_rq           : std_logic_vector(BRANCH_COUNT-1 downto 0);
   signal ticket_vld          : std_logic_vector(BRANCH_COUNT-1 downto 0);
   signal ticket_full         : std_logic_vector(BRANCH_COUNT-1 downto 0);

   -- FL Splitter input
   signal split_rx_data        : std_logic_vector(HGEN_DATA_WIDTH-1 downto 0);
   signal split_rx_rem         : std_logic_vector(log2(HGEN_DATA_WIDTH/8)-1 downto 0);
   signal split_rx_sof_n       : std_logic;
   signal split_rx_eof_n       : std_logic;
   signal split_rx_sop_n       : std_logic;
   signal split_rx_eop_n       : std_logic;
   signal split_rx_src_rdy_n   : std_logic;
   signal split_rx_dst_rdy_n   : std_logic;

   -- FL Splitter output
   signal split_tx_data        : std_logic_vector(BRANCH_COUNT*HGEN_DATA_WIDTH-1 downto 0);
   signal split_tx_rem         : std_logic_vector(BRANCH_COUNT*log2(HGEN_DATA_WIDTH/8)-1 downto 0);
   signal split_tx_sof_n       : std_logic_vector(BRANCH_COUNT-1 downto 0);
   signal split_tx_eof_n       : std_logic_vector(BRANCH_COUNT-1 downto 0);
   signal split_tx_sop_n       : std_logic_vector(BRANCH_COUNT-1 downto 0);
   signal split_tx_eop_n       : std_logic_vector(BRANCH_COUNT-1 downto 0);
   signal split_tx_src_rdy_n   : std_logic_vector(BRANCH_COUNT-1 downto 0);
   signal split_tx_dst_rdy_n   : std_logic_vector(BRANCH_COUNT-1 downto 0);

   -- FL Sequencer input
   signal seq_rx_data        : std_logic_vector(BRANCH_COUNT*HGEN_DATA_WIDTH-1 downto 0);
   signal seq_rx_rem         : std_logic_vector(BRANCH_COUNT*log2(HGEN_DATA_WIDTH/8)-1 downto 0);
   signal seq_rx_sof_n       : std_logic_vector(BRANCH_COUNT-1 downto 0);
   signal seq_rx_eof_n       : std_logic_vector(BRANCH_COUNT-1 downto 0);
   signal seq_rx_sop_n       : std_logic_vector(BRANCH_COUNT-1 downto 0);
   signal seq_rx_eop_n       : std_logic_vector(BRANCH_COUNT-1 downto 0);
   signal seq_rx_src_rdy_n   : std_logic_vector(BRANCH_COUNT-1 downto 0);
   signal seq_rx_dst_rdy_n   : std_logic_vector(BRANCH_COUNT-1 downto 0);

   -- FL Sequencer output
   signal seq_tx_data        : std_logic_vector(HGEN_DATA_WIDTH-1 downto 0);
   signal seq_tx_rem         : std_logic_vector(log2(HGEN_DATA_WIDTH/8)-1 downto 0);
   signal seq_tx_sof_n       : std_logic;
   signal seq_tx_eof_n       : std_logic;
   signal seq_tx_sop_n       : std_logic;
   signal seq_tx_eop_n       : std_logic;
   signal seq_tx_src_rdy_n   : std_logic;
   signal seq_tx_dst_rdy_n   : std_logic;

begin

   -- input transformer
   input_trans_i: entity work.FL_TRANSFORMER
   generic map(
      -- the data width of the data input
      RX_DATA_WIDTH  => DATA_WIDTH,
      TX_DATA_WIDTH  => HGEN_DATA_WIDTH
   )
   port map(
      -- common signals
      -- global FGPA clock
      CLK               => CLK,

      -- global synchronous reset
      RESET             => RESET,

      -- RX Framelink interface
      RX_DATA           => RX_DATA,
      RX_REM            => RX_REM,
      RX_SOP_N          => RX_SOP_N,
      RX_EOP_N          => RX_EOP_N,
      RX_SOF_N          => RX_SOF_N,
      RX_EOF_N          => RX_EOF_N,
      RX_SRC_RDY_N      => RX_SRC_RDY_N,
      RX_DST_RDY_N      => RX_DST_RDY_N,

      -- TX FrameLink interface
      TX_DATA           => split_rx_data,
      TX_REM            => split_rx_rem,
      TX_SOP_N          => split_rx_sop_n,
      TX_EOP_N          => split_rx_eop_n,
      TX_SOF_N          => split_rx_sof_n,
      TX_EOF_N          => split_rx_eof_n,
      TX_SRC_RDY_N      => split_rx_src_rdy_n,
      TX_DST_RDY_N      => split_rx_dst_rdy_n
   );

   -- Ticket counter
   cnt_ticketp: process(CLK)
   begin
      if (CLK'event and CLK='1') then
         if RESET = '1' then
            cnt_ticket <= (others => '0');
         elsif cnt_ticket_ce = '1' then
            cnt_ticket <= cnt_ticket + 1;
         end if;
      end if;
   end process;

   cnt_ticket_vld <= '1';
   ticket_rq <= not ticket_full;

   -- Ticket splitter
   splitter: entity work.FL_TICKET_SPLITTER_FIFO2NFIFO
      generic map (
         RX_DATA_WIDTH     => HGEN_DATA_WIDTH,
         TX_DATA_WIDTH     => HGEN_DATA_WIDTH,
         OUTPUT_COUNT      => BRANCH_COUNT,
         FRAME_PARTS       => INPUT_PARTS,
         TICKET_WIDTH      => TICKET_WIDTH,
         TICKET_FIFO_ITEMS => TICKET_FIFO_ITEMS
      )
      port map (
         CLK            => CLK,
         RESET          => RESET,

         -- input interface
         RX_DATA        => split_rx_data,
         RX_REM         => split_rx_rem,
         RX_SOF_N       => split_rx_sof_n,
         RX_EOF_N       => split_rx_eof_n,
         RX_SOP_N       => split_rx_sop_n,
         RX_EOP_N       => split_rx_eop_n,
         RX_SRC_RDY_N   => split_rx_src_rdy_n,
         RX_DST_RDY_N   => split_rx_dst_rdy_n,

         -- Input ticket (control) interface
         CTRL_DATA_IN      => cnt_ticket,
         CTRL_DATA_IN_VLD  => cnt_ticket_vld,
         CTRL_DATA_IN_RQ   => cnt_ticket_ce,

         -- output interface
         TX_DATA        => split_tx_data,
         TX_REM         => split_tx_rem,
         TX_SOF_N       => split_tx_sof_n,
         TX_EOF_N       => split_tx_eof_n,
         TX_SOP_N       => split_tx_sop_n,
         TX_EOP_N       => split_tx_eop_n,
         TX_SRC_RDY_N   => split_tx_src_rdy_n,
         TX_DST_RDY_N   => split_tx_dst_rdy_n,

         -- Output ticket (control) interface
         CTRL_DATA_OUT     => ticket,
         CTRL_DATA_OUT_VLD => ticket_vld,
         CTRL_DATA_OUT_RQ  => ticket_rq
      );


gen_hgen: for i in 0 to BRANCH_COUNT-1 generate 
      -- HGEN verification cover
      hgen_ver_cover_i: entity work.HGEN_VER_COVER
      generic map(
         -- the data width of the data input/output
         DATA_WIDTH     => HGEN_DATA_WIDTH,
         USE_BRAMS_FOR_HGEN_FIFO => USE_BRAMS_FOR_HGEN_FIFO
      )
      port map(
         -- common signals
         -- global FGPA clock
         CLK               => CLK,

         -- global synchronous reset
         RESET             => RESET,
         
         -- RX Framelink interface
         RX_DATA           => split_tx_data((i+1)*HGEN_DATA_WIDTH-1 downto
         i*HGEN_DATA_WIDTH),
         RX_REM            => split_tx_rem((i+1)*log2(HGEN_DATA_WIDTH/8)-1
         downto i*log2(HGEN_DATA_WIDTH/8)),
         RX_SRC_RDY_N      => split_tx_src_rdy_n(i),
         RX_DST_RDY_N      => split_tx_dst_rdy_n(i),
         RX_SOP_N          => split_tx_sop_n(i),
         RX_EOP_N          => split_tx_eop_n(i),
         RX_SOF_N          => split_tx_sof_n(i),
         RX_EOF_N          => split_tx_eof_n(i),

         -- TX FrameLink interface
         TX_DATA           => seq_rx_data((i+1)*HGEN_DATA_WIDTH-1 downto
         i*HGEN_DATA_WIDTH),
         TX_REM            => seq_rx_rem((i+1)*log2(HGEN_DATA_WIDTH/8)-1
         downto i*log2(HGEN_DATA_WIDTH/8)),
         TX_SRC_RDY_N      => seq_rx_src_rdy_n(i),
         TX_DST_RDY_N      => seq_rx_dst_rdy_n(i),
         TX_SOP_N          => seq_rx_sop_n(i),
         TX_EOP_N          => seq_rx_eop_n(i),
         TX_SOF_N          => seq_rx_sof_n(i),
         TX_EOF_N          => seq_rx_eof_n(i)
      ); 
   end generate;

   -- Ticket sequencer
   sequencer: entity work.FL_TICKET_SEQUENCER
      generic map (
         INPUT_WIDTH          => HGEN_DATA_WIDTH,
         INPUT_COUNT          => BRANCH_COUNT,
         OUTPUT_WIDTH         => HGEN_DATA_WIDTH,
         PARTS                => BRANCH_PARTS,
         TICKET_WIDTH         => TICKET_WIDTH,
         TICKET_FIFO_ITEMS    => TICKET_FIFO_ITEMS
      )
      port map (
         CLK               => CLK,
         RESET             => RESET,

         -- input FrameLink interface
         RX_DATA        => seq_rx_data,
         RX_REM         => seq_rx_rem,
         RX_SOF_N       => seq_rx_sof_n,
         RX_EOF_N       => seq_rx_eof_n,
         RX_SOP_N       => seq_rx_sop_n,
         RX_EOP_N       => seq_rx_eop_n,
         RX_SRC_RDY_N   => seq_rx_src_rdy_n,
         RX_DST_RDY_N   => seq_rx_dst_rdy_n,

         TICKET         => ticket,
         TICKET_WR      => ticket_vld,
         TICKET_FULL    => ticket_full,

         -- output FrameLink interface
         TX_DATA        => seq_tx_data,
         TX_REM         => seq_tx_rem,
         TX_SOF_N       => seq_tx_sof_n,
         TX_EOF_N       => seq_tx_eof_n,
         TX_SOP_N       => seq_tx_sop_n,
         TX_EOP_N       => seq_tx_eop_n,
         TX_SRC_RDY_N   => seq_tx_src_rdy_n,
         TX_DST_RDY_N   => seq_tx_dst_rdy_n
      );

   -- output transformer
   output_trans_i: entity work.FL_TRANSFORMER
   generic map(
      -- the data width of the data input
      RX_DATA_WIDTH  => HGEN_DATA_WIDTH,
      TX_DATA_WIDTH  => DATA_WIDTH
   )
   port map(
      -- common signals
      -- global FGPA clock
      CLK               => CLK,

      -- global synchronous reset
      RESET             => RESET,

      -- RX Framelink interface
      RX_DATA           => seq_tx_data,
      RX_REM            => seq_tx_rem,
      RX_SOP_N          => seq_tx_sop_n,
      RX_EOP_N          => seq_tx_eop_n,
      RX_SOF_N          => seq_tx_sof_n,
      RX_EOF_N          => seq_tx_eof_n,
      RX_SRC_RDY_N      => seq_tx_src_rdy_n,
      RX_DST_RDY_N      => seq_tx_dst_rdy_n,

      -- TX FrameLink interface
      TX_DATA           => TX_DATA,
      TX_REM            => TX_REM,
      TX_SOP_N          => TX_SOP_N,
      TX_EOP_N          => TX_EOP_N,
      TX_SOF_N          => TX_SOF_N,
      TX_EOF_N          => TX_EOF_N,
      TX_SRC_RDY_N      => TX_SRC_RDY_N,
      TX_DST_RDY_N      => TX_DST_RDY_N
   );

end architecture;
