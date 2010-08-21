-- cutter_tb.vhd: FrameLink cutter testbench
-- Copyright (C) 2007 CESNET
-- Author(s): Michal Trs <trsm1@liberouter.org>
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
-- $Id:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;
use work.fl_pkg.all;
use work.fl_sim_oper.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture testbench_arch of testbench is


-- -----------------------Testbench constant-----------------------------------
   constant clkper_50   : time := 20 ns;
   constant clkper_100  : time := 10 ns;
   constant reset_time  : time := 50 * clkper_100;
   constant DATA_WIDTH  : integer := 32;
   constant RX_LOG      : string :="./data/rx_log.txt";
   constant TX_LOG      : string :="./data/tx_log.txt";
   constant HEADER      : boolean := true;
   constant FOOTER      : boolean := true;
   constant FRAME_PARTS : integer := 3;
   constant OFFSET      : integer := 3;
   constant SIZE        : integer := 2;
   constant CUT_HDR     : boolean := true;
   constant CUT_PLD     : boolean := false;
   constant CUT_FTR     : boolean := false;

-- -----------------------Testbench auxilarity signals-------------------------
   -- CLK_GEN Signals
   signal reset               : std_logic;
   signal clk                 : std_logic;
   signal clk_50_in           : std_logic;
   signal clk50               : std_logic;
   signal clk100              : std_logic;
   signal lock                : std_logic;
   signal fl_clk              : std_logic;

   -- Frame Link Bus 32
   signal FL_bus_sim2cut      : t_fl32;
   signal FL_bus_cut2sim      : t_fl32;

   -- FL Sim TX signals
   signal fl_sim_ctrl_tx      : t_fl_ctrl;
   signal fl_sim_strobe_tx    : std_logic;
   signal fl_sim_busy_tx      : std_logic;

   -- FL Sim RX signals
   signal fl_sim_ctrl_rx      : t_fl_ctrl;
   signal fl_sim_strobe_rx    : std_logic;
   signal fl_sim_busy_rx      : std_logic;


begin

-- Reset generation -----------------------------------------------------------
   reset_gen : process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process reset_gen;

-- clk50 generator ------------------------------------------------------------
clk50_gen : process
begin
   clk_50_in <= '1';
   wait for clkper_50/2;
   clk_50_in <= '0';
   wait for clkper_50/2;
end process;

-- CLK_GEN component ----------------------------------------------------------
CLK_GEN_U: entity work.CLK_GEN
   port map (
      -- Input
      CLK50_IN    => clk_50_in,
      RESET       => '0',
      -- Output
      CLK50_OUT   => clk50,
      CLK25       => open,
      CLK100      => clk100,
      CLK200      => open,
      LOCK        => lock
   );
clk <= clk100;
fl_clk <= clk100;

-- CLK_GEN component ----------------------------------------------------------
UUT: entity work.FL_CUTTER
   generic map (
      -- Frame link width
      DATA_WIDTH   => DATA_WIDTH,
      -- Header / Footer data present
      HEADER       => HEADER,
      FOOTER       => FOOTER,
      -- Remove part options
      OFFSET       => OFFSET,
      SIZE         => SIZE,
      CUT_HDR      => CUT_HDR,
      CUT_PLD      => CUT_PLD,
      CUT_FTR      => CUT_FTR
   )
   port map(
      CLK          => fl_clk,
      RESET        => reset,
      -- Write interface
      RX_DATA        => FL_bus_sim2cut.DATA,
      RX_REM         => FL_bus_sim2cut.DREM,
      RX_SOF_N       => FL_bus_sim2cut.SOF_N,
      RX_EOF_N       => FL_bus_sim2cut.EOF_N,
      RX_SOP_N       => FL_bus_sim2cut.SOP_N,
      RX_EOP_N       => FL_bus_sim2cut.EOP_N,
      RX_SRC_RDY_N   => FL_bus_sim2cut.SRC_RDY_N,
      RX_DST_RDY_N   => FL_bus_sim2cut.DST_RDY_N,
      -- Read interface
      TX_DATA        => FL_bus_cut2sim.DATA,
      TX_REM         => FL_bus_cut2sim.DREM,
      TX_SOF_N       => FL_bus_cut2sim.SOF_N,
      TX_EOF_N       => FL_bus_cut2sim.EOF_N,
      TX_SOP_N       => FL_bus_cut2sim.SOP_N,
      TX_EOP_N       => FL_bus_cut2sim.EOP_N,
      TX_SRC_RDY_N   => FL_bus_cut2sim.SRC_RDY_N,
      TX_DST_RDY_N   => FL_bus_cut2sim.DST_RDY_N
   );

-- Frame Link Bus simulation component ----------------------------------------
FL_SIM_TX_U : entity work.FL_SIM
   generic map (
      DATA_WIDTH     => DATA_WIDTH,
      FRAME_PARTS    => FRAME_PARTS,
      TX_LOG_FILE    => TX_LOG
   )
   port map (
      -- Common interface
      FL_RESET       => reset,
      FL_CLK         => fl_clk,

      -- FL Bus Interface
      RX_DATA        => (others => '0'),
      RX_REM         => (others => '0'),
      RX_SOF_N       => '1',
      RX_EOF_N       => '1',
      RX_SOP_N       => '1',
      RX_EOP_N       => '1',
      RX_SRC_RDY_N   => '1',
      RX_DST_RDY_N   => open,

      TX_DATA        => FL_bus_sim2cut.DATA,
      TX_REM         => FL_bus_sim2cut.DREM,
      TX_SOF_N       => FL_bus_sim2cut.SOF_N,
      TX_EOF_N       => FL_bus_sim2cut.EOF_N,
      TX_SOP_N       => FL_bus_sim2cut.SOP_N,
      TX_EOP_N       => FL_bus_sim2cut.EOP_N,
      TX_SRC_RDY_N   => FL_bus_sim2cut.SRC_RDY_N,
      TX_DST_RDY_N   => FL_bus_sim2cut.DST_RDY_N,

      -- IB SIM interface
      CTRL           => fl_sim_ctrl_tx,
      STROBE         => fl_sim_strobe_tx,
      BUSY           => fl_sim_busy_tx
   );


FL_SIM_RX_U: entity work.FL_SIM
      generic map (
         DATA_WIDTH     => DATA_WIDTH,
         FRAME_PARTS    => FRAME_PARTS,
         RX_LOG_FILE    => RX_LOG
      )
      port map (
         -- Common interface
         FL_RESET       => RESET,
         FL_CLK         => CLK,

         -- FrameLink Interface
         RX_DATA        =>FL_bus_cut2sim.DATA,
         RX_REM         =>FL_bus_cut2sim.DREM,
         RX_SOF_N       =>FL_bus_cut2sim.SOF_N,
         RX_EOF_N       =>FL_bus_cut2sim.EOF_N,
         RX_SOP_N       =>FL_bus_cut2sim.SOP_N,
         RX_EOP_N       =>FL_bus_cut2sim.EOP_N,
         RX_SRC_RDY_N   =>FL_bus_cut2sim.SRC_RDY_N,
         RX_DST_RDY_N   =>FL_bus_cut2sim.DST_RDY_N,

         TX_DATA        => open,
         TX_REM         => open,
         TX_SOF_N       => open,
         TX_EOF_N       => open,
         TX_SOP_N       => open,
         TX_EOP_N       => open,
         TX_SRC_RDY_N   => open,
         TX_DST_RDY_N   => '0',

         -- FL SIM interface
         CTRL           => fl_sim_ctrl_rx,
         STROBE         => fl_sim_strobe_rx,
         BUSY           => fl_sim_busy_rx
      );


   tb : process
      -- support function
      procedure fl_op_tx(ctrl : in t_fl_ctrl) is
      begin
         wait until (clk'event and clk='1' and fl_sim_busy_tx = '0');
         fl_sim_ctrl_tx <= ctrl;
         fl_sim_strobe_tx <= '1';
         wait until (clk'event and clk='1');
         fl_sim_strobe_tx <= '0';
      end fl_op_tx;

      -- support function
      procedure fl_op_rx(ctrl : in t_fl_ctrl) is
      begin
         wait until (clk'event and clk='1' and fl_sim_busy_rx = '0');
         fl_sim_ctrl_rx <= ctrl;
         fl_sim_strobe_rx <= '1';
         wait until (clk'event and clk='1');
         fl_sim_strobe_rx <= '0';
      end fl_op_rx;


   begin
      FL_bus_cut2sim.DST_RDY_N <= '0';
      wait for 3*reset_time;
      
      fl_op_tx(fl_send32("./data/packet1.txt"));
      wait;
   end process;

end architecture testbench_arch;
