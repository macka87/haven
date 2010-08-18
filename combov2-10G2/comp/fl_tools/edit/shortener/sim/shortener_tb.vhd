-- shortener_tb.vhd: Testbench for FrameLink Shortener
-- Copyright (C) 2008 CESNET
-- Author(s): Michal Kajan <xkajan01@stud.fit.vutbr.cz>
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
use work.fl_bfm_rdy_pkg.all;
use work.FL_BFM_pkg.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   -- constants declarations
   ----------------------------------------------------------------------------
   constant DATA_WIDTH        : integer := 64;
   constant PARTS             : integer := 3;
   -- note that you must use correct data input/output file for simulation;
   -- at the end of file is specified data input file as parameter for function
   -- SendWriteFile, and 3 directories are prepared with 3 different files representing
   -- data input with different number of parts in frame
   -- name of directory is represented with number - this number represent
   -- number of parts of frame generated from given file
   constant PART_NUM          : integer := 1;
   constant BYTES_KEPT        : integer := 15;

   constant clkper            : time := 10 ns; 
   constant reset_time        : time := 100 ns;
   constant idle_time         : time := 150 ns;
   constant wait_time         : time := 50 ns;

   constant fl_bfm_id  : integer := 0;     -- ID of fl_bfm component   

   -- signals declarations
   ----------------------------------------------------------------------------
   signal clk                 : std_logic;
   signal reset               : std_logic;
   
   -- UUT input signals
   signal fl_shortener_rx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_shortener_rx_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_shortener_rx_sof_n     : std_logic;
   signal fl_shortener_rx_sop_n     : std_logic;
   signal fl_shortener_rx_eop_n     : std_logic;
   signal fl_shortener_rx_eof_n     : std_logic;
   signal fl_shortener_rx_src_rdy_n : std_logic;
   signal fl_shortener_rx_dst_rdy_n : std_logic;

   -- UUT output signals
   signal fl_shortener_tx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_shortener_tx_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_shortener_tx_sof_n     : std_logic;
   signal fl_shortener_tx_sop_n     : std_logic;
   signal fl_shortener_tx_eof_n     : std_logic;
   signal fl_shortener_tx_eop_n     : std_logic;
   signal fl_shortener_tx_src_rdy_n : std_logic;
   signal fl_shortener_tx_dst_rdy_n : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                   FL Shortener
   -- -------------------------------------------------------------------------
   uut: entity work.FL_SHORTENER
      generic map (
         DATA_WIDTH        => DATA_WIDTH,
         PART_NUM          => PART_NUM,
         BYTES_KEPT        => BYTES_KEPT,
         PARTS             => PARTS
      )
      port map (
         CLK               => CLK,
         RESET             => RESET,

         RX_DATA           => fl_shortener_rx_data,
         RX_REM            => fl_shortener_rx_rem,
         RX_SOF_N          => fl_shortener_rx_sof_n,
         RX_SOP_N          => fl_shortener_rx_sop_n,
         RX_EOP_N          => fl_shortener_rx_eop_n,
         RX_EOF_N          => fl_shortener_rx_eof_n,
         RX_SRC_RDY_N      => fl_shortener_rx_src_rdy_n,
         RX_DST_RDY_N      => fl_shortener_rx_dst_rdy_n,

         TX_DATA           => fl_shortener_tx_data,
         TX_REM            => fl_shortener_tx_rem,
         TX_SOF_N          => fl_shortener_tx_sof_n,
         TX_SOP_N          => fl_shortener_tx_sop_n,
         TX_EOP_N          => fl_shortener_tx_eop_n,
         TX_EOF_N          => fl_shortener_tx_eof_n,
         TX_SRC_RDY_N      => fl_shortener_tx_src_rdy_n,
         TX_DST_RDY_N      => fl_shortener_tx_dst_rdy_n
      );

   
   -- -------------------------------------------------------------------------
   --                   FL Simulation Component
   -- -------------------------------------------------------------------------
   fl_bfm_0: entity work.fl_bfm
      generic map(
         DATA_WIDTH      => data_width,
         FL_BFM_ID       => fl_bfm_id
      )
      port map(
         CLK          => clk,
         RESET        => reset,
 
         TX_DATA      => fl_shortener_rx_data,
         TX_REM       => fl_shortener_rx_rem,
         TX_SRC_RDY_N => fl_shortener_rx_src_rdy_n,
         TX_DST_RDY_N => fl_shortener_rx_dst_rdy_n,
         TX_SOP_N     => fl_shortener_rx_sop_n,
         TX_EOP_N     => fl_shortener_rx_eop_n,
         TX_SOF_N     => fl_shortener_rx_sof_n,
         TX_EOF_N     => fl_shortener_rx_eof_n         
      )
   ;
   
   monitor: entity work.monitor
      generic map(
         RX_TX_DATA_WIDTH  => data_width,
         FILE_NAME         => "./3/fl_out.txt",
         FRAME_PARTS       => 3,
         RDY_DRIVER        => RND
      )
      port map(
         FL_RESET          => reset,
         FL_CLK            => clk,
         
         RX_DATA           => fl_shortener_tx_data,
         RX_REM            => fl_shortener_tx_rem,
         RX_SOF_N          => fl_shortener_tx_sof_n,
         RX_EOF_N          => fl_shortener_tx_eof_n,
         RX_SOP_N          => fl_shortener_tx_sop_n,
         RX_EOP_N          => fl_shortener_tx_eop_n,
         RX_SRC_RDY_N      => fl_shortener_tx_src_rdy_n,
         RX_DST_RDY_N      => fl_shortener_tx_dst_rdy_n
      )
   ;

      
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

   begin
      wait for 3*reset_time;
       SendWriteFile("./3/fl_sim_send.txt", RND, flCmd_0, 0);

      wait;
   end process;
end architecture behavioral;
