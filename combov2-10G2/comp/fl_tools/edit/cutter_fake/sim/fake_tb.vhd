-- fake_tb.vhd: FL_CUTTER (fake) testbench file
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Louda <sandin@liberouter.org>
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
use ieee.numeric_std.all;
use ieee.std_logic_arith.all;

-- package with FL records
use work.fl_pkg.all;

-- FL BFM and monitor packages
use work.fl_sim_oper.all;
use work.fl_bfm_rdy_pkg.all;
use work.FL_BFM_pkg.all;


entity testbench is
end testbench;

architecture testbench of testbench is

constant CLKPER   : time   := 10 ns;

signal clk        : std_logic;
signal reset      : std_logic;

signal fl_rx      : t_fl128;
signal fl_tx      : t_fl128;
signal cut_data   : std_logic_vector(15 downto 0);
signal cut_vld    : std_logic;
signal fl_rx_16   : t_fl16;
signal fl_tx_16   : t_fl16;
signal cut_data_16: std_logic_vector(15 downto 0);
signal cut_vld_16 : std_logic;

signal monitor_src_rdy : std_logic;
signal monitor_dst_rdy : std_logic;

begin

uut: entity work.fl_cutter_fake
   generic map(
      OFFSET         => 0
   )
   port map(
      CLK            => clk,
      RESET          => reset,
      --
      CUTTED_DATA    => cut_data,
      CUTTED_VLD     => cut_vld,
      --
      RX_DATA        => fl_rx.data,
      RX_REM         => fl_rx.drem,
      RX_SOF_N       => fl_rx.sof_n,
      RX_EOF_N       => fl_rx.eof_n,
      RX_SOP_N       => fl_rx.sop_n,
      RX_EOP_N       => fl_rx.eop_n,
      RX_SRC_RDY_N   => fl_rx.src_rdy_n,
      RX_DST_RDY_N   => fl_rx.dst_rdy_n,
      --
      TX_DATA        => fl_tx.data,
      TX_REM         => fl_tx.drem,
      TX_SOF_N       => fl_tx.sof_n,
      TX_EOF_N       => fl_tx.eof_n,
      TX_SOP_N       => fl_tx.sop_n,
      TX_EOP_N       => fl_tx.eop_n,
      TX_SRC_RDY_N   => fl_tx.src_rdy_n,
      TX_DST_RDY_N   => fl_tx.dst_rdy_n
   );

uut_16: entity work.fl_cutter_fake
   generic map(
      -- (Changed by polcak_l to demonstrate a bug that has been found)
      DATA_WIDTH     => 16,
      OFFSET         => 2,
      PART           => 1,
      SIZE           => 2
   )
   port map(
      CLK            => clk,
      RESET          => reset,
      --
      CUTTED_DATA    => cut_data_16,
      CUTTED_VLD     => cut_vld_16,
      --
      RX_DATA        => fl_rx_16.data,
      RX_REM         => fl_rx_16.drem,
      RX_SOF_N       => fl_rx_16.sof_n,
      RX_EOF_N       => fl_rx_16.eof_n,
      RX_SOP_N       => fl_rx_16.sop_n,
      RX_EOP_N       => fl_rx_16.eop_n,
      RX_SRC_RDY_N   => fl_rx_16.src_rdy_n,
      RX_DST_RDY_N   => fl_rx_16.dst_rdy_n,
      --
      TX_DATA        => fl_tx_16.data,
      TX_REM         => fl_tx_16.drem,
      TX_SOF_N       => fl_tx_16.sof_n,
      TX_EOF_N       => fl_tx_16.eof_n,
      TX_SOP_N       => fl_tx_16.sop_n,
      TX_EOP_N       => fl_tx_16.eop_n,
      TX_SRC_RDY_N   => fl_tx_16.src_rdy_n,
      TX_DST_RDY_N   => fl_tx_16.dst_rdy_n
   );

   -- -------------------------------------------------------------------------
   --                   FL Simulation Component - RX
   -- -------------------------------------------------------------------------
   fl_monitor: entity work.monitor
      generic map (
         RX_TX_DATA_WIDTH  => 16,
         FILE_NAME         => "./fl_monitor.txt",
         FRAME_PARTS       => 2,
         RDY_DRIVER        => EVER
      )
      port map (
         -- Common interface
         FL_RESET          => RESET,
         FL_CLK            => CLK,

         -- RX Frame link Interface
         RX_DATA           => fl_tx_16.data,
         RX_REM            => fl_tx_16.drem,
         RX_SOF_N          => fl_tx_16.sof_n,
         RX_EOF_N          => fl_tx_16.eof_n,
         RX_SOP_N          => fl_tx_16.sop_n,
         RX_EOP_N          => fl_tx_16.eop_n,
         RX_SRC_RDY_N      => monitor_src_rdy,
         RX_DST_RDY_N      => monitor_dst_rdy
      );

   monitor_src_rdy <= fl_tx_16.src_rdy_n or fl_tx_16.dst_rdy_n;


clkgen: process
   begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
   end process;

tb: process
begin

   -- idle
   fl_rx.data        <= (others => '0');
   fl_rx.drem        <= (others => '1');
   fl_rx.sof_n       <= '1';
   fl_rx.eof_n       <= '1';
   fl_rx.sop_n       <= '1';
   fl_rx.eop_n       <= '1';
   fl_rx.src_rdy_n   <= '1';

   fl_tx.dst_rdy_n   <= '0';

   reset <= '1';
   wait for 0.1 us;
   wait for 6 ns;
   reset <= '0';
   wait for 10*clkper;

   -- frame 1
   -- header
   fl_rx.data        <= X"11100011100011100011100011100011";
   fl_rx.drem        <= (others => '1');
   fl_rx.sof_n       <= '0';
   fl_rx.eof_n       <= '1';
   fl_rx.sop_n       <= '0';
   fl_rx.eop_n       <= '0';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;
   -- payload
   fl_rx.data        <= X"abcdefabcdefabcdefabcdefabcdefab";
   fl_rx.drem        <= (others => '1');
   fl_rx.sof_n       <= '1';
   fl_rx.eof_n       <= '0';
   fl_rx.sop_n       <= '0';
   fl_rx.eop_n       <= '0';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;
   -- end of frame

   fl_rx.src_rdy_n   <= '1';
   wait for clkper;

   -- frame 2
   -- header
   fl_rx.data        <= X"11100011100011100011100011100011";
   fl_rx.drem        <= (others => '1');
   fl_rx.sof_n       <= '0';
   fl_rx.eof_n       <= '1';
   fl_rx.sop_n       <= '0';
   fl_rx.eop_n       <= '1';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx.data        <= X"11100011100011100011100011100011";
   fl_rx.drem        <= (others => '1');
   fl_rx.sof_n       <= '1';
   fl_rx.eof_n       <= '1';
   fl_rx.sop_n       <= '1';
   fl_rx.eop_n       <= '0';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;
   -- payload
   fl_rx.data        <= X"abcdefabcdefabcdefabcdefabcdefab";
   fl_rx.drem        <= (others => '1');
   fl_rx.sof_n       <= '1';
   fl_rx.eof_n       <= '0';
   fl_rx.sop_n       <= '0';
   fl_rx.eop_n       <= '0';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;
   -- end of frame

   fl_rx.src_rdy_n   <= '1';
   wait for clkper;

   -- frame 3
   -- header
   fl_rx.data        <= X"11100011100011100011100011100011";
   fl_rx.drem        <= (others => '1');
   fl_rx.sof_n       <= '0';
   fl_rx.eof_n       <= '1';
   fl_rx.sop_n       <= '0';
   fl_rx.eop_n       <= '1';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx.data        <= X"11100011100011100011100011100011";
   fl_rx.drem        <= (others => '1');
   fl_rx.sof_n       <= '1';
   fl_rx.eof_n       <= '1';
   fl_rx.sop_n       <= '1';
   fl_rx.eop_n       <= '0';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;
   -- payload
   fl_rx.data        <= X"abcdefabcdefabcdefabcdefabcdefab";
   fl_rx.drem        <= (others => '1');
   fl_rx.sof_n       <= '1';
   fl_rx.eof_n       <= '1';
   fl_rx.sop_n       <= '0';
   fl_rx.eop_n       <= '1';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx.data        <= X"fedcbafedcbafedcbafedcbafedcbafe";
   fl_rx.drem        <= (others => '1');
   fl_rx.sof_n       <= '1';
   fl_rx.eof_n       <= '0';
   fl_rx.sop_n       <= '1';
   fl_rx.eop_n       <= '0';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;
   -- end of frame

   fl_rx.src_rdy_n   <= '1';
   wait for clkper;

   -- frame 4
   -- header
   fl_rx.data        <= X"11100011100011100011100011100011";
   fl_rx.drem        <= (others => '1');
   fl_rx.sof_n       <= '0';
   fl_rx.eof_n       <= '1';
   fl_rx.sop_n       <= '0';
   fl_rx.eop_n       <= '1';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx.data        <= X"11100011100011100011100011100011";
   fl_rx.drem        <= (others => '1');
   fl_rx.sof_n       <= '1';
   fl_rx.eof_n       <= '1';
   fl_rx.sop_n       <= '1';
   fl_rx.eop_n       <= '0';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;
   -- payload
   fl_rx.data        <= X"abcdefabcdefabcdefabcdefabcdefab";
   fl_rx.drem        <= (others => '1');
   fl_rx.sof_n       <= '1';
   fl_rx.eof_n       <= '1';
   fl_rx.sop_n       <= '0';
   fl_rx.eop_n       <= '1';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx.data        <= X"fedcbafedcbafedcbafedcbafedcbafe";
   fl_rx.drem        <= "0001";
   fl_rx.sof_n       <= '1';
   fl_rx.eof_n       <= '0';
   fl_rx.sop_n       <= '1';
   fl_rx.eop_n       <= '0';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;
   -- end of frame

   fl_rx.src_rdy_n   <= '1';
   wait for clkper;

   -- frame 5
   -- header
   fl_rx.data        <= X"11100011100011100011100011100011";
   fl_rx.drem        <= (others => '1');
   fl_rx.sof_n       <= '0';
   fl_rx.eof_n       <= '1';
   fl_rx.sop_n       <= '0';
   fl_rx.eop_n       <= '1';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx.data        <= X"11100011100011100011100011100011";
   fl_rx.drem        <= (others => '1');
   fl_rx.sof_n       <= '1';
   fl_rx.eof_n       <= '1';
   fl_rx.sop_n       <= '1';
   fl_rx.eop_n       <= '0';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;
   -- payload
   fl_rx.data        <= X"abcdefabcdefabcdefabcdefabcdefab";
   fl_rx.drem        <= (others => '1');
   fl_rx.sof_n       <= '1';
   fl_rx.eof_n       <= '1';
   fl_rx.sop_n       <= '0';
   fl_rx.eop_n       <= '1';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx.data        <= X"fedcbafedcbafedcbafedcbafedcbafe";
   fl_rx.drem        <= "0010";
   fl_rx.sof_n       <= '1';
   fl_rx.eof_n       <= '0';
   fl_rx.sop_n       <= '1';
   fl_rx.eop_n       <= '0';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;
   -- end of frame

   fl_rx.src_rdy_n   <= '1';
   wait for 10*clkper;

   -- frame 6
   -- header
   fl_rx.data        <= X"11100011100011100011100011100011";
   fl_rx.drem        <= (others => '1');
   fl_rx.sof_n       <= '0';
   fl_rx.eof_n       <= '1';
   fl_rx.sop_n       <= '0';
   fl_rx.eop_n       <= '1';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx.src_rdy_n   <= '1';
   wait for clkper;
   fl_rx.data        <= X"11100011100011100011100011100011";
   fl_rx.drem        <= (others => '1');
   fl_rx.sof_n       <= '1';
   fl_rx.eof_n       <= '1';
   fl_rx.sop_n       <= '1';
   fl_rx.eop_n       <= '0';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;

   fl_tx.dst_rdy_n   <= '1';

   -- payload
   fl_rx.data        <= X"abcdefabcdefabcdefabcdefabcdefab";
   fl_rx.drem        <= (others => '1');
   fl_rx.sof_n       <= '1';
   fl_rx.eof_n       <= '1';
   fl_rx.sop_n       <= '0';
   fl_rx.eop_n       <= '1';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;
   fl_tx.dst_rdy_n   <= '0';
   wait for clkper;
   fl_tx.dst_rdy_n   <= '1';
   fl_rx.data        <= X"fedcbafedcbafedcbafedcbafedcbafe";
--    fl_rx.drem        <= (others => '1');
   fl_rx.drem        <= "0001";
   fl_rx.sof_n       <= '1';
   fl_rx.eof_n       <= '0';
   fl_rx.sop_n       <= '1';
   fl_rx.eop_n       <= '0';
   fl_rx.src_rdy_n   <= '0';
   wait for clkper;
   fl_tx.dst_rdy_n   <= '0';
   wait for clkper;
   -- end of frame

   fl_rx.src_rdy_n   <= '1';
--    fl_tx.dst_rdy_n   <= '1';
   wait for clkper;

   -- idle
   fl_rx.data        <= (others => '0');
   fl_rx.drem        <= (others => '1');
   fl_rx.sof_n       <= '1';
   fl_rx.eof_n       <= '1';
   fl_rx.sop_n       <= '1';
   fl_rx.eop_n       <= '1';
   fl_rx.src_rdy_n   <= '1';

   fl_tx.dst_rdy_n   <= '0';

   wait;
   end process;


-- -------------------------------------------------------------------------
--                   FL Cutter 16
-- -------------------------------------------------------------------------
tb_16: process
begin

   -- idle
   fl_rx_16.data        <= (others => '0');
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '1';
   fl_rx_16.eop_n       <= '1';
   fl_rx_16.src_rdy_n   <= '1';

   fl_tx_16.dst_rdy_n   <= '0';

   wait for 202 ns;

   -- frame 1
   -- header
   fl_rx_16.data        <= X"1234";
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '0';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '0';
   fl_rx_16.eop_n       <= '0';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   -- payload
   fl_rx_16.data        <= X"abcd";
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '0';
   fl_rx_16.eop_n       <= '1';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx_16.data        <= X"ef01";
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '1';
   fl_rx_16.eop_n       <= '1';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx_16.data        <= X"2345";
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '1';
   fl_rx_16.eop_n       <= '1';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx_16.data        <= X"6789";
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '0';
   fl_rx_16.sop_n       <= '1';
   fl_rx_16.eop_n       <= '0';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   -- end of frame

   fl_rx_16.src_rdy_n   <= '1';
   wait for clkper;

   -- frame 2
   -- header
   fl_rx_16.data        <= X"1234";
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '0';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '0';
   fl_rx_16.eop_n       <= '1';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx_16.data        <= X"5678";
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '1';
   fl_rx_16.eop_n       <= '0';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   -- payload
   fl_rx_16.data        <= X"abcd";
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '0';
   fl_rx_16.eop_n       <= '1';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx_16.data        <= X"efef";
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '1';
   fl_rx_16.eop_n       <= '1';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx_16.data        <= X"ef01";
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '0';
   fl_rx_16.sop_n       <= '1';
   fl_rx_16.eop_n       <= '0';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   -- end of frame

   fl_rx_16.src_rdy_n   <= '1';
   wait for clkper;
   wait for clkper;

   -- frame 3
   -- header
   fl_rx_16.data        <= X"1234";
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '0';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '0';
   fl_rx_16.eop_n       <= '1';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx_16.data        <= X"5678";
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '1';
   fl_rx_16.eop_n       <= '0';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   -- payload
   fl_rx_16.data        <= X"abcd";
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '0';
   fl_rx_16.eop_n       <= '1';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx_16.data        <= X"efef";
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '1';
   fl_rx_16.eop_n       <= '1';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx_16.data        <= X"ef01";
   fl_rx_16.drem        <= "0";
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '0';
   fl_rx_16.sop_n       <= '1';
   fl_rx_16.eop_n       <= '0';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   -- end of frame

   fl_rx_16.src_rdy_n   <= '1';
   wait for clkper;

   -- frame 4
   -- header
   fl_rx_16.data        <= X"1234";
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '0';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '0';
   fl_rx_16.eop_n       <= '1';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx_16.data        <= X"5678";
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '1';
   fl_rx_16.eop_n       <= '0';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;

   -- payload
   fl_rx_16.data        <= X"abcd";
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '0';
   fl_rx_16.eop_n       <= '1';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx_16.data        <= X"ef01";
--    fl_rx_16.drem        <= (others => '1');
   fl_rx_16.drem        <= "0";
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '1';
   fl_rx_16.eop_n       <= '1';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx_16.data        <= X"ef02";
--    fl_rx_16.drem        <= (others => '1');
   fl_rx_16.drem        <= "0";
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '0';
   fl_rx_16.sop_n       <= '1';
   fl_rx_16.eop_n       <= '0';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   -- end of frame

   -- frame 5
   -- header
   fl_rx_16.data        <= X"1234";
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '0';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '0';
   fl_rx_16.eop_n       <= '1';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   fl_rx_16.data        <= X"5678";
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '1';
   fl_rx_16.eop_n       <= '0';
   fl_rx_16.src_rdy_n   <= '0';
   fl_tx_16.dst_rdy_n   <= '1';
   wait for clkper;
   wait for 10*clkper;
   fl_tx_16.dst_rdy_n   <= '0';
   wait for clkper;

   -- payload
   fl_rx_16.data        <= X"abcd";
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '0';
   fl_rx_16.eop_n       <= '1';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   fl_tx_16.dst_rdy_n   <= '0';
   wait for clkper;
   fl_tx_16.dst_rdy_n   <= '1';
   fl_rx_16.data        <= X"ef01";
--    fl_rx_16.drem        <= (others => '1');
   fl_rx_16.drem        <= "0";
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '0';
   fl_rx_16.sop_n       <= '1';
   fl_rx_16.eop_n       <= '0';
   fl_rx_16.src_rdy_n   <= '0';
   wait for clkper;
   fl_tx_16.dst_rdy_n   <= '0';
   wait for clkper;
   -- end of frame

   fl_rx_16.src_rdy_n   <= '1';
--    fl_tx_16.dst_rdy_n   <= '1';
   wait for clkper;


   -- idle
   fl_rx_16.data        <= (others => '0');
   fl_rx_16.drem        <= (others => '1');
   fl_rx_16.sof_n       <= '1';
   fl_rx_16.eof_n       <= '1';
   fl_rx_16.sop_n       <= '1';
   fl_rx_16.eop_n       <= '1';
   fl_rx_16.src_rdy_n   <= '1';

   fl_tx_16.dst_rdy_n   <= '0';

   wait;
   end process;

end;
