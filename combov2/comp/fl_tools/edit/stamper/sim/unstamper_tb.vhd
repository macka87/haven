-- unstamper_tb.vhd: Testbench for FrameLink Stamper
-- Copyright (C) 2008 CESNET
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
use work.fl_sim_oper.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is
   
   -- FL_UNSTAMPER generics
   constant DATA_WIDTH           : integer := 16;
      
   -- TEST properties
   constant clkper               : time := 10 ns;
   constant reset_time           : time := 10 * clkper;
   
   -- ------------------ Signals declaration ----------------------------------
   signal clk              : std_logic;
   signal reset            : std_logic;
   
   -- input interface
   signal rx_sof_n         : std_logic;
   signal rx_sop_n         : std_logic;
   signal rx_eop_n         : std_logic;
   signal rx_eof_n         : std_logic;
   signal rx_src_rdy_n     : std_logic;
   signal rx_dst_rdy_n     : std_logic;
   signal rx_data          : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal rx_rem           : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   
   -- output interface
   signal tx_sof_n         : std_logic;
   signal tx_sop_n         : std_logic;
   signal tx_eop_n         : std_logic;
   signal tx_eof_n         : std_logic;
   signal tx_src_rdy_n     : std_logic;
   signal tx_dst_rdy_n     : std_logic;
   signal tx_data          : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal tx_rem           : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

   -- FL Sim signals
   signal filename         : t_fl_ctrl;
   signal fl_sim_strobe    : std_logic;
   signal fl_sim_busy      : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- UUT
   UUT : entity work.FL_UNSTAMPER
      generic map(
         DATA_WIDTH     => DATA_WIDTH
      )
      port map(
         CLK            => clk,
         RESET          => reset,
         -- input interface
         RX_SOF_N       => rx_sof_n,
         RX_SOP_N       => rx_sop_n,
         RX_EOP_N       => rx_eop_n,
         RX_EOF_N       => rx_eof_n,
         RX_SRC_RDY_N   => rx_src_rdy_n,
         RX_DST_RDY_N   => rx_dst_rdy_n,
         RX_DATA        => rx_data,
         RX_REM         => rx_rem,
         -- output interface
         TX_SOF_N       => tx_sof_n,
         TX_SOP_N       => tx_sop_n,
         TX_EOP_N       => tx_eop_n,
         TX_EOF_N       => tx_eof_n,
         TX_SRC_RDY_N   => tx_src_rdy_n,
         TX_DST_RDY_N   => tx_dst_rdy_n,
         TX_DATA        => tx_data,
         TX_REM         => tx_rem
      );

   -- -------------------------------------------------------------------------
   --                    FL Simulation Components
   -- -------------------------------------------------------------------------
   fl_sim: entity work.FL_SIM
      generic map (
         DATA_WIDTH     => DATA_WIDTH,
         RX_LOG_FILE    => "",
         TX_LOG_FILE    => "",
         FRAME_PARTS    => 2
      )
      port map (
         -- Common interface
         FL_RESET       => reset,
         FL_CLK         => clk,
         -- Frame link Interface
         RX_DATA        => (others => '0'),
         RX_REM         => (others => '0'),
         RX_SOF_N       => '1',
         RX_EOF_N       => '1',
         RX_SOP_N       => '1',
         RX_EOP_N       => '1',
         RX_SRC_RDY_N   => '1', -- Source isn't ready
         RX_DST_RDY_N   => open,
         TX_DATA        => rx_data,
         TX_REM         => rx_rem,
         TX_SOF_N       => rx_sof_n,
         TX_EOF_N       => rx_eof_n,
         TX_SOP_N       => rx_sop_n,
         TX_EOP_N       => rx_eop_n,
         TX_SRC_RDY_N   => rx_src_rdy_n,
         TX_DST_RDY_N   => rx_dst_rdy_n,
         -- FL SIM interface
         CTRL           => filename,
         STROBE         => fl_sim_strobe,
         BUSY           => fl_sim_busy
      );

   -- clock generator ---------------------------------------------------------
   clk_gen : process
   begin
      clk <= '1';
      wait for clkper/2;
      clk <= '0';
      wait for clkper/2;
   end process;

   -- Reset generation --------------------------------------------------------
   reset_gen : process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process reset_gen;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb : process
   -- This procedure must be placed in this testbench file. Using this
   -- procedure is necessery for corect function of FL_SIM 
   procedure send_packet(ctrl : in t_fl_ctrl) is
   begin
      wait until (clk'event and clk='1' and fl_sim_busy = '0');
      filename <= ctrl;
      fl_sim_strobe <= '1';
      wait until (clk'event and clk='1');
      fl_sim_strobe <= '0';
   end send_packet;

begin
   tx_dst_rdy_n   <= '1';

   wait for reset_time;
   tx_dst_rdy_n   <= '0';

   -- send packets
   send_packet(fl_send32("packet1.txt"));
   send_packet(fl_send32("packet1.txt"));

   wait for 6*clkper;
   wait until clk'event and clk='1';
   tx_dst_rdy_n   <= '1';
   wait until clk'event and clk='1';
   tx_dst_rdy_n   <= '0';

   send_packet(fl_send32("packet1.txt"));
   send_packet(fl_send32("packet1.txt"));
   
   wait;
end process;

end architecture behavioral;
