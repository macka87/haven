-- testbench.vhd: Testbench for FL Composer
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
   constant clkper            : time := 10 ns; 
   constant reset_time        : time := 10*clkper;
   constant idle_time         : time := 2*reset_time;

   constant FL_WIDTH          : integer := 64;
   constant CTRL_HDR_EN       : boolean := false;
   constant CTRL_FTR_EN       : boolean := false;
   constant FL_RELAY          : boolean := true;

   -- Signals declaration
   signal clk                 : std_logic;
   signal reset               : std_logic;
   
   -- UUT input signals
   signal rx_data             : std_logic_vector(FL_WIDTH-1 downto 0);
   signal rx_rem              : std_logic_vector(log2(FL_WIDTH/8)-1 downto 0);
   signal rx_sop_n            : std_logic;
   signal rx_eop_n            : std_logic;
   signal rx_src_rdy_n        : std_logic;
   signal rx_dst_rdy_n        : std_logic;
   signal rx_hdata            : std_logic_vector(FL_WIDTH-1 downto 0);
   signal rx_hrem             : std_logic_vector(log2(FL_WIDTH/8)-1 downto 0);
   signal rx_hsop_n           : std_logic;
   signal rx_heop_n           : std_logic;
   signal rx_hsrc_rdy_n       : std_logic;
   signal rx_hdst_rdy_n       : std_logic;

   -- UUT output signals
   signal tx_data             : std_logic_vector(FL_WIDTH-1 downto 0);
   signal tx_rem              : std_logic_vector(log2(FL_WIDTH/8)-1 downto 0);
   signal tx_sop_n            : std_logic;
   signal tx_eop_n            : std_logic;
   signal tx_sof_n            : std_logic;
   signal tx_eof_n            : std_logic;
   signal tx_src_rdy_n        : std_logic;
   signal tx_dst_rdy_n        : std_logic;

   -- FL SIM TX signals
   signal flsim_tx_data       : std_logic_vector(FL_WIDTH-1 downto 0);
   signal flsim_tx_rem        : std_logic_vector(log2(FL_WIDTH/8)-1 downto 0);
   signal flsim_tx_sop_n      : std_logic;
   signal flsim_tx_sof_n      : std_logic;
   signal flsim_tx_eop_n      : std_logic;
   signal flsim_tx_eof_n      : std_logic;
   signal flsim_tx_src_rdy_n  : std_logic;
   signal flsim_tx_dst_rdy_n  : std_logic;

   signal filename_tx         : t_fl_ctrl;
   signal fl_sim_strobe_tx    : std_logic;
   signal fl_sim_busy_tx      : std_logic;

   -- FL Sim RX signals
   signal filename_rx         : t_fl_ctrl;
   signal fl_sim_strobe_rx    : std_logic;
   signal fl_sim_busy_rx      : std_logic;


-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                     FL Composer
   -- -------------------------------------------------------------------------
   uut: entity work.fl_composer
      generic map (
         CTRL_HDR_EN       => CTRL_HDR_EN,
         CTRL_FTR_EN       => CTRL_FTR_EN,
         FL_WIDTH_TX       => FL_WIDTH,
         FL_RELAY          => FL_RELAY
      )
      port map (
         CLK               => CLK,
         RESET             => RESET,
   
         RX_DATA           => rx_data,
         RX_REM            => rx_rem,
         RX_SOP_N          => rx_sop_n,
         RX_EOP_N          => rx_eop_n,
         RX_SRC_RDY_N      => rx_src_rdy_n,
         RX_DST_RDY_N      => rx_dst_rdy_n,
   
         RX_HDATA          => rx_hdata,
         RX_HREM           => rx_hrem,
         RX_HSOP_N         => rx_hsop_n,
         RX_HEOP_N         => rx_heop_n,
         RX_HSRC_RDY_N     => rx_hsrc_rdy_n,
         RX_HDST_RDY_N     => rx_hdst_rdy_n,
   
         TX_DATA           => tx_data,
         TX_REM            => tx_rem,
         TX_SOF_N          => tx_sof_n,
         TX_SOP_N          => tx_sop_n,
         TX_EOP_N          => tx_eop_n,
         TX_EOF_N          => tx_eof_n,
         TX_SRC_RDY_N      => tx_src_rdy_n,
         TX_DST_RDY_N      => tx_dst_rdy_n
      );
   -- -------------------------------------------------------------------------
   --                   FL Simulation Component - TX
   -- -------------------------------------------------------------------------
   fl_sim_tx: entity work.FL_SIM
      generic map (
         DATA_WIDTH     => FL_WIDTH,
         TX_LOG_FILE    => "fl_sim_tx.txt"
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
         DATA_WIDTH     => FL_WIDTH,
         RX_LOG_FILE    => "fl_sim_rx.txt"
      )
      port map (
         -- Common interface
         FL_RESET       => RESET,
         FL_CLK         => CLK,
   
         -- FrameLink Interface
         RX_DATA        => tx_data,
         RX_REM         => tx_rem,
         RX_SOF_N       => tx_sof_n,
         RX_EOF_N       => tx_eof_n,
         RX_SOP_N       => tx_sop_n,
         RX_EOP_N       => tx_eop_n,
         RX_SRC_RDY_N   => tx_src_rdy_n,
         RX_DST_RDY_N   => tx_dst_rdy_n,
   
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

   -- ----------------------------------------------------
   rx_data        <= flsim_tx_data;
   rx_rem         <= flsim_tx_rem;
   rx_sop_n       <= flsim_tx_sop_n;
   rx_eop_n       <= flsim_tx_eop_n;
   rx_src_rdy_n   <= flsim_tx_src_rdy_n;

   rx_hdata       <= flsim_tx_data;
   rx_hrem        <= flsim_tx_rem;
   rx_hsop_n      <= flsim_tx_sop_n;
   rx_heop_n      <= flsim_tx_eop_n;
   rx_hsrc_rdy_n  <= flsim_tx_src_rdy_n;

   flsim_tx_dst_rdy_n <= rx_dst_rdy_n and rx_hdst_rdy_n;

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
