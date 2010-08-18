-- marker_tb.vhd: FrameLink Marker testbench.
-- Copyright (C) 2006 CESNET
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
-- $Id$
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

   -- uut configuration
   constant clkper_50   : time := 20 ns;
   constant clkper_100  : time := 10 ns;
   constant reset_time  : time := 50 * clkper_100;
   constant RX_LOG      : string :="";
   constant TX_LOG      : string :="./data/fl_sim_tx.txt";
   constant OFFSET      : integer := 3;
   constant SIZE        : integer := 2;
   constant DATA_WIDTH  : integer := 16;
   constant HEADER      : boolean := true;
   constant FOOTER      : boolean := true;
   constant MARK_HDR    : boolean := true;
   constant MARK_FTR    : boolean := false;
   constant INSERT      : boolean := true;

-- -----------------------Testbench auxilarity signals-------------------------
   -- Frame Link Bus
   signal FL_bus_sim2mark     : t_fl16;
   signal FL_bus_mark2sim     : t_fl16;

   -- CLK_GEN Signals
   signal reset               : std_logic;
   signal clk                 : std_logic;
   signal clk_50_in           : std_logic;
   signal clk50               : std_logic;
   signal clk100              : std_logic;
   signal lock                : std_logic;
   signal fl_clk              : std_logic;

   -- FL_SIM component ctrl
   signal fl_sim_ctrl         : t_fl_ctrl;
   signal fl_sim_strobe       : std_logic;
   signal fl_sim_busy         : std_logic;
   signal fl_sim_ctrl1        : t_fl_ctrl;
   signal fl_sim_strobe1      : std_logic;
   signal fl_sim_busy1        : std_logic;

   -- Marker signals
   signal mark          : std_logic_vector(SIZE*8-1 downto 0):= (others => '0');
   signal mark_next     : std_logic;


-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

-- Reset generation --
   reset_gen : process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process reset_gen;

-- clk50 generator --
   clk50_gen : process
   begin
      clk_50_in <= '1';
      wait for clkper_50/2;
      clk_50_in <= '0';
      wait for clkper_50/2;
   end process;

-- CLK_GEN component --
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


   UUT: entity work.fl_marker
   generic map (
      DATA_WIDTH   => DATA_WIDTH,
      HEADER       => HEADER,
      FOOTER       => FOOTER,
      OFFSET       => OFFSET,
      SIZE         => SIZE,
      MARK_HDR     => MARK_HDR,
      MARK_FTR     => MARK_FTR,
      INSERT       => INSERT
   )
   port map (
      CLK          => fl_clk,
      RESET        => reset,
      MARK         => mark,
      MARK_NEXT    => mark_next,
      -- Write interface
      RX_DATA      => FL_bus_sim2mark.DATA,
      RX_REM       => FL_bus_sim2mark.DREM,
      RX_SOF_N     => FL_bus_sim2mark.SOF_N,
      RX_EOF_N     => FL_bus_sim2mark.EOF_N,
      RX_SOP_N     => FL_bus_sim2mark.SOP_N,
      RX_EOP_N     => FL_bus_sim2mark.EOP_N,
      RX_SRC_RDY_N => FL_bus_sim2mark.SRC_RDY_N,
      RX_DST_RDY_N => FL_bus_sim2mark.DST_RDY_N,
      -- Read interface
      TX_DATA      => FL_bus_mark2sim.DATA,
      TX_REM       => FL_bus_mark2sim.DREM,
      TX_SOF_N     => FL_bus_mark2sim.SOF_N,
      TX_EOF_N     => FL_bus_mark2sim.EOF_N,
      TX_SOP_N     => FL_bus_mark2sim.SOP_N,
      TX_EOP_N     => FL_bus_mark2sim.EOP_N,
      TX_SRC_RDY_N => FL_bus_mark2sim.SRC_RDY_N,
      TX_DST_RDY_N => FL_bus_mark2sim.DST_RDY_N
   );


   -- mark generator --
   makrgen: process(mark_next)
   begin
      if mark_next = '1' then
         mark <= mark + '1';
      end if;
   end process;


-- Frame Link Bus simulation component ----------------------------------------
   FL_SIM_U : entity work.FL_SIM
   generic map (
      DATA_WIDTH     => DATA_WIDTH,
      RX_LOG_FILE    => RX_LOG,
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

      TX_DATA        => FL_bus_sim2mark.DATA,
      TX_REM         => FL_bus_sim2mark.DREM,
      TX_SOF_N       => FL_bus_sim2mark.SOF_N,
      TX_EOF_N       => FL_bus_sim2mark.EOF_N,
      TX_SOP_N       => FL_bus_sim2mark.SOP_N,
      TX_EOP_N       => FL_bus_sim2mark.EOP_N,
      TX_SRC_RDY_N   => FL_bus_sim2mark.SRC_RDY_N,
      TX_DST_RDY_N   => FL_bus_sim2mark.DST_RDY_N,

      -- IB SIM interface
      CTRL           => fl_sim_ctrl,
      STROBE         => fl_sim_strobe,
      BUSY           => fl_sim_busy
   );

   tb : process
      -- support function
      procedure fl_op(ctrl : in t_fl_ctrl) is
      begin
         wait until (FL_CLK'event and FL_CLK='1' and fl_sim_busy = '0');
         fl_sim_ctrl <= ctrl;
         fl_sim_strobe <= '1';
         wait until (FL_CLK'event and FL_CLK='1');
         fl_sim_strobe <= '0';
      end fl_op;

   begin
      -- ready to receive
      FL_bus_mark2sim.DST_RDY_N <= '0';

      -- Testbench
      fl_sim_strobe <= '0';
      wait for reset_time;
      fl_op(fl_send32("./data/fl_sim_send.txt"));
   end process;

end architecture testbench_arch;
