-- sequencer_tb.vhd: Testbench for FrameLink Sequencer
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

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;
use work.fl_sim_oper.all; -- FrameLink Simulation Package

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is
   -- Constant declaration
   constant INPUT_WIDTH       : integer := 16;
   constant INPUT_COUNT       : integer := 3;
   constant OUTPUT_WIDTH      : integer := 64;
   constant HEADER            : boolean := false;
   constant FOOTER            : boolean := true;
   constant PARTS             : integer := 2;
   constant TICKET_PART       : integer := 1;
   constant TICKET_HDR        : boolean := false;
   constant TICKET_PLD        : boolean := false;
   constant TICKET_FTR        : boolean := true;
   constant TICKET_OFFSET     : integer := 0;
   constant TICKET_SIZE       : integer := 2;
   constant TICKET_FIFO_ITEMS : integer := 16;
   constant INPUT_FIFO_ITEMS  : integer := 128;
   constant OUTPUT_FIFO_ITEMS : integer := 128;

   constant clkper            : time := 10 ns; 
   constant reset_time        : time := 100 ns;
   constant idle_time         : time := 150 ns;
   constant wait_time         : time := 50 ns;

   -- Signals declaration
   signal clk                 : std_logic;
   signal reset               : std_logic;
   
   -- UUT input signals
   signal sequencer_rx_data      : std_logic_vector(INPUT_COUNT*INPUT_WIDTH-1 
                                                                     downto 0);
   signal sequencer_rx_rem       : std_logic_vector
                                 (INPUT_COUNT*log2(INPUT_WIDTH/8)-1 downto 0);
   signal sequencer_rx_sof_n     : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal sequencer_rx_sop_n     : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal sequencer_rx_eop_n     : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal sequencer_rx_eof_n     : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal sequencer_rx_src_rdy_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal sequencer_rx_dst_rdy_n : std_logic_vector(INPUT_COUNT-1 downto 0);

   -- UUT output signals
   signal sequencer_tx_data   : std_logic_vector(OUTPUT_WIDTH-1 downto 0);
   signal sequencer_tx_rem    : std_logic_vector(log2(OUTPUT_WIDTH/8)-1 downto 0);
   signal sequencer_tx_sof_n  : std_logic;
   signal sequencer_tx_sop_n  : std_logic;
   signal sequencer_tx_eof_n  : std_logic;
   signal sequencer_tx_eop_n  : std_logic;
   signal sequencer_tx_src_rdy_n : std_logic;
   signal sequencer_tx_dst_rdy_n : std_logic;

   -- FL Sim signals
   signal flsim_tx_data       : std_logic_vector(INPUT_WIDTH-1 downto 0);
   signal flsim_tx_rem        :
                           std_logic_vector(log2(INPUT_WIDTH/8) - 1 downto 0);
   signal flsim_tx_sof_n      : std_logic;
   signal flsim_tx_sop_n      : std_logic;
   signal flsim_tx_eop_n      : std_logic;
   signal flsim_tx_eof_n      : std_logic;
   signal flsim_tx_src_rdy_n  : std_logic;
   signal flsim_tx_dst_rdy_n  : std_logic;

   -- FL Sim TX signals
   signal filename_tx         : t_fl_ctrl;
   signal fl_sim_strobe_tx    : std_logic;
   signal fl_sim_busy_tx      : std_logic;

   -- FL Sim RX signals
   signal filename_rx         : t_fl_ctrl;
   signal fl_sim_strobe_rx    : std_logic;
   signal fl_sim_busy_rx      : std_logic;

   -- FL Sim RX signals
   signal filename_mar        : t_fl_ctrl;
   signal fl_sim_strobe_mar   : std_logic;
   signal fl_sim_busy_mar      : std_logic;

   -- FL Marker tx signals
   signal flmarker_tx_data       : std_logic_vector(INPUT_WIDTH-1 downto 0);
   signal flmarker_tx_rem        :
                           std_logic_vector(log2(INPUT_WIDTH/8) - 1 downto 0);
   signal flmarker_tx_sof_n      : std_logic;
   signal flmarker_tx_sop_n      : std_logic;
   signal flmarker_tx_eop_n      : std_logic;
   signal flmarker_tx_eof_n      : std_logic;
   signal flmarker_tx_src_rdy_n  : std_logic;
   signal flmarker_tx_dst_rdy_n  : std_logic;

   -- FL Marker tx signals
   signal flmarkersim_tx_data       : std_logic_vector(INPUT_WIDTH-1 downto 0);
   signal flmarkersim_tx_rem        :
                           std_logic_vector(log2(INPUT_WIDTH/8) - 1 downto 0);
   signal flmarkersim_tx_sof_n      : std_logic;
   signal flmarkersim_tx_sop_n      : std_logic;
   signal flmarkersim_tx_eop_n      : std_logic;
   signal flmarkersim_tx_eof_n      : std_logic;
   signal flmarkersim_tx_src_rdy_n  : std_logic;
   signal flmarkersim_tx_dst_rdy_n  : std_logic;

   -- Ticket generator signals
   signal ticket_generator       : std_logic_vector(TICKET_SIZE*8-1 downto 0);
   signal ticket_generator_ce    : std_logic;
-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                   FL SEQUENCER
   -- -------------------------------------------------------------------------
   uut: entity work.FL_SEQUENCER
      generic map (
         INPUT_WIDTH          => INPUT_WIDTH,
         INPUT_COUNT          => INPUT_COUNT,
         OUTPUT_WIDTH         => OUTPUT_WIDTH,
         PARTS                => PARTS,
         TICKET_PART          => TICKET_PART,
         TICKET_OFFSET        => TICKET_OFFSET,
         TICKET_SIZE          => TICKET_SIZE,
         TICKET_FIFO_ITEMS    => TICKET_FIFO_ITEMS,
         INPUT_FIFO_ITEMS     => INPUT_FIFO_ITEMS,
         OUTPUT_FIFO_ITEMS    => OUTPUT_FIFO_ITEMS
      )
      port map (
         CLK               => CLK,
         RESET             => RESET,
         RX_SOF_N          => sequencer_rx_sof_n,
         RX_SOP_N          => sequencer_rx_sop_n,
         RX_EOP_N          => sequencer_rx_eop_n,
         RX_EOF_N          => sequencer_rx_eof_n,
         RX_SRC_RDY_N      => sequencer_rx_src_rdy_n,
         RX_DST_RDY_N      => sequencer_rx_dst_rdy_n,
         RX_DATA           => sequencer_rx_data,
         RX_REM            => sequencer_rx_rem,
         TX_SOF_N          => sequencer_tx_sof_n,
         TX_SOP_N          => sequencer_tx_sop_n,
         TX_EOP_N          => sequencer_tx_eop_n,
         TX_EOF_N          => sequencer_tx_eof_n,
         TX_SRC_RDY_N      => sequencer_tx_src_rdy_n,
         TX_DST_RDY_N      => sequencer_tx_dst_rdy_n,
         TX_DATA           => sequencer_tx_data,
         TX_REM            => sequencer_tx_rem
      );

   -- -------------------------------------------------------------------------
   --                   FL Simulation Component - TX
   -- -------------------------------------------------------------------------
   fl_sim_tx: entity work.FL_SIM
      generic map (
         DATA_WIDTH     => INPUT_WIDTH,
         TX_LOG_FILE    => "fl_sim_tx.txt",
         FRAME_PARTS    => PARTS
      )
      port map (
         -- Common interface
         FL_RESET       => RESET,
         FL_CLK         => CLK,
   
         -- Frame link Interface
         RX_DATA        => (others => '0'),
         RX_REM         => (others => '0'),
         RX_SOF_N       => '1',
         RX_EOF_N       => '1',
         RX_SOP_N       => '1',
         RX_EOP_N       => '1',
         RX_SRC_RDY_N   => '1',
         RX_DST_RDY_N   => open,
   
         TX_DATA        => flsim_tx_data,
         TX_REM         => flsim_tx_rem,
         TX_SOF_N       => flsim_tx_sof_n,
         TX_EOF_N       => flsim_tx_eof_n,
         TX_SOP_N       => flsim_tx_sop_n,
         TX_EOP_N       => flsim_tx_eop_n,
         TX_SRC_RDY_N   => flsim_tx_src_rdy_n,
         TX_DST_RDY_N   => flsim_tx_dst_rdy_n,
   
         -- FL SIM interface
         CTRL           => filename_tx,
         STROBE         => fl_sim_strobe_tx,
         BUSY           => fl_sim_busy_tx
      );
   
   -- -------------------------------------------------------------------------
   --                   FL Simulation Component - RX
   -- -------------------------------------------------------------------------
   fl_sim_rx: entity work.FL_SIM
      generic map (
         DATA_WIDTH     => OUTPUT_WIDTH,
         RX_LOG_FILE    => "fl_sim_rx.txt",
         FRAME_PARTS    => PARTS
      )
      port map (
         -- Common interface
         FL_RESET       => RESET,
         FL_CLK         => CLK,
   
         -- FrameLink Interface
         RX_DATA        => sequencer_tx_data,
         RX_REM         => sequencer_tx_rem,
         RX_SOF_N       => sequencer_tx_sof_n,
         RX_EOF_N       => sequencer_tx_eof_n,
         RX_SOP_N       => sequencer_tx_sop_n,
         RX_EOP_N       => sequencer_tx_eop_n,
         RX_SRC_RDY_N   => sequencer_tx_src_rdy_n,
         RX_DST_RDY_N   => sequencer_tx_dst_rdy_n,
   
         TX_DATA        => open,
         TX_REM         => open,
         TX_SOF_N       => open,
         TX_EOF_N       => open,
         TX_SOP_N       => open,
         TX_EOP_N       => open,
         TX_SRC_RDY_N   => open,
         TX_DST_RDY_N   => '0',
   
         -- FL SIM interface
         CTRL           => filename_rx,
         STROBE         => fl_sim_strobe_rx,
         BUSY           => fl_sim_busy_rx
      );
      
   -- -------------------------------------------------------------------------
   --                FL Simulation Component - after Marker
   -- -------------------------------------------------------------------------
   fl_sim_after_marker: entity work.FL_SIM
      generic map (
         DATA_WIDTH     => INPUT_WIDTH,
         RX_LOG_FILE    => "fl_sim_marker.txt",
         FRAME_PARTS    => PARTS
      )
      port map (
         -- Common interface
         FL_RESET       => RESET,
         FL_CLK         => CLK,
   
         -- FrameLink Interface
         RX_DATA        => flmarker_tx_data,
         RX_REM         => flmarker_tx_rem,
         RX_SOF_N       => flmarker_tx_sof_n,
         RX_EOF_N       => flmarker_tx_eof_n,
         RX_SOP_N       => flmarker_tx_sop_n,
         RX_EOP_N       => flmarker_tx_eop_n,
         RX_SRC_RDY_N   => flmarker_tx_src_rdy_n,
         RX_DST_RDY_N   => flmarker_tx_dst_rdy_n,
   
         TX_DATA        => flmarkersim_tx_data,
         TX_REM         => flmarkersim_tx_rem,
         TX_SOF_N       => flmarkersim_tx_sof_n,
         TX_EOF_N       => flmarkersim_tx_eof_n,
         TX_SOP_N       => flmarkersim_tx_sop_n,
         TX_EOP_N       => flmarkersim_tx_eop_n,
         TX_SRC_RDY_N   => flmarkersim_tx_src_rdy_n,
         TX_DST_RDY_N   => flmarkersim_tx_dst_rdy_n,
   
         -- FL SIM interface
         CTRL           => filename_mar,
         STROBE         => fl_sim_strobe_mar,
         BUSY           => fl_sim_busy_mar
      );
      
   -- -------------------------------------------------------------------------
   --                   FL Marker
   -- -------------------------------------------------------------------------
   fl_marker: entity work.FL_MARKER
      generic map (
         -- Frame link width
         DATA_WIDTH     => INPUT_WIDTH,
         -- Header / Footer data present
         HEADER         => HEADER,
         FOOTER         => FOOTER,
         -- Mark options
         OFFSET         => TICKET_OFFSET,
         SIZE           => TICKET_SIZE,
         -- Add "mark" to header or footer (only one can be selected)
         MARK_HDR       => TICKET_HDR,
         MARK_FTR       => TICKET_FTR,
         -- architecture switch (false = ReWrite, true = Insert)
         INSERT         => true
      )
      port map (
         CLK            => CLK,
         RESET          => RESET,
         -- Ticket insertation
         MARK           => ticket_generator,
         MARK_NEXT      => ticket_generator_ce,
         -- Input interface
         RX_DATA        => flsim_tx_data,
         RX_REM         => flsim_tx_rem,
         RX_SRC_RDY_N   => flsim_tx_src_rdy_n,
         RX_DST_RDY_N   => flsim_tx_dst_rdy_n,
         RX_SOP_N       => flsim_tx_sop_n,
         RX_EOP_N       => flsim_tx_eop_n,
         RX_SOF_N       => flsim_tx_sof_n,
         RX_EOF_N       => flsim_tx_eof_n,
         -- Output interface
         TX_DATA        => flmarker_tx_data,
         TX_REM         => flmarker_tx_rem,
         TX_SRC_RDY_N   => flmarker_tx_src_rdy_n,
         TX_DST_RDY_N   => flmarker_tx_dst_rdy_n,
         TX_SOP_N       => flmarker_tx_sop_n,
         TX_EOP_N       => flmarker_tx_eop_n,
         TX_SOF_N       => flmarker_tx_sof_n,
         TX_EOF_N       => flmarker_tx_eof_n
      );

   -- -------------------------------------------------------------------------
   --                   Ticket generator
   -- -------------------------------------------------------------------------
   ticket_generatorp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         ticket_generator <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (ticket_generator_ce = '1') then
            ticket_generator <= ticket_generator + 1;
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   --                   FL Splitter
   -- -------------------------------------------------------------------------
   fl_splitter: entity work.FL_SPLITTER
      generic map (
         DATA_WIDTH     => INPUT_WIDTH,
         OUTPUT_COUNT   => INPUT_COUNT,
         FRAME_PARTS    => PARTS
      )
      port map (
         CLK               => CLK,
         RESET             => RESET,
         -- input interface
         RX_SOF_N       => flmarkersim_tx_sof_n,
         RX_SOP_N       => flmarkersim_tx_sop_n,
         RX_EOP_N       => flmarkersim_tx_eop_n,
         RX_EOF_N       => flmarkersim_tx_eof_n,
         RX_SRC_RDY_N   => flmarkersim_tx_src_rdy_n,
         RX_DST_RDY_N   => flmarkersim_tx_dst_rdy_n,
         RX_DATA        => flmarkersim_tx_data,
         RX_REM         => flmarkersim_tx_rem,
         -- output interface
         TX_SOF_N       => sequencer_rx_sof_n,
         TX_SOP_N       => sequencer_rx_sop_n,
         TX_EOP_N       => sequencer_rx_eop_n,
         TX_EOF_N       => sequencer_rx_eof_n,
         TX_SRC_RDY_N   => sequencer_rx_src_rdy_n,
         TX_DST_RDY_N   => sequencer_rx_dst_rdy_n,
         TX_DATA        => sequencer_rx_data,
         TX_REM         => sequencer_rx_rem
      );


   -- ----------------------------------------------------
   -- CLK generator
   clkgen: process
   begin
      clk <= '1';
      wait for clkper/2;
      clk <= '0';
      wait for clkper/2;
   end process;

   resetgen: process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process;

   tb: process
      -- This procedure must be placed in this testbench file. Using this
      -- procedure is necessery for corect function of FL_SIM 
      procedure fl_op_tx(ctrl : in t_fl_ctrl) is
      begin
         wait until (clk'event and clk='1' and fl_sim_busy_tx = '0');
         filename_tx <= ctrl;
         fl_sim_strobe_tx <= '1';
         wait until (clk'event and clk='1');
         fl_sim_strobe_tx <= '0';
      end fl_op_tx;

      -- This procedure must be placed in this testbench file. Using this
      -- procedure is necessery for corect function of FL_SIM 
      procedure fl_op_rx(ctrl : in t_fl_ctrl) is
      begin
         wait until (clk'event and clk='1' and fl_sim_busy_rx = '0');
         filename_rx <= ctrl;
         fl_sim_strobe_rx <= '1';
         wait until (clk'event and clk='1');
         fl_sim_strobe_rx <= '0';
      end fl_op_rx;

   begin
      wait for 3*reset_time;
      fl_op_tx(fl_send32("./fl_sim_send.txt"));

      wait;
   end process;
end architecture behavioral;
