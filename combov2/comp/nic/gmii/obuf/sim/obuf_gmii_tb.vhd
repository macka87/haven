--
-- top_level_tb.vhd: Testbench for obuf gmii
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
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
--
library ieee;
use ieee.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

use work.math_pack.all;
use work.obuf_pkg.all;
use work.fl_sim_oper.all; -- FrameLink Simulation Package
use work.fl_pkg.ALL;
use work.lb_pkg.all; 
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is
   
   -- constants affecting testbench ------------------------
   constant data_paths   : integer := 1;
   constant ctrl_cmd     : boolean := true;
   constant max_data     : integer := 25;
   constant pkt_count    : integer := 20;

   constant gmii_clkper  : time := 8 ns;
   constant wr_clkper    : time := 5 ns;
   constant reset_time           : time := 10 * wr_clkper;

   signal reset      : std_logic;
   signal wrclk      : std_logic;
   signal refclk     : std_logic;
   signal data       : std_logic_vector((data_paths*8)-1 downto 0);
   signal drem       : std_logic_vector(log2(data_paths)-1 downto 0);
   signal src_rdy_n  : std_logic;
   signal sof_n      : std_logic;
   signal sop_n      : std_logic;
   signal eof_n      : std_logic;
   signal eop_n      : std_logic;
   signal dst_rdy_n  : std_logic;

   signal txclk      : std_logic;
   signal txd        : std_logic_vector(7 downto 0);
   signal txen       : std_logic;
   signal txer       : std_logic;

   signal adc_clk    : std_logic;
   signal adc_rd     : std_logic;
   signal adc_wr     : std_logic;
   signal adc_addr   : std_logic_vector(5 downto 0);
   signal adc_di     : std_logic_vector(31 downto 0);
   signal adc_do     : std_logic_vector(31 downto 0);
   signal adc_drdy   : std_logic;

   signal obuf0_tx         : t_fl64;
   signal obuf1_tx         : t_fl64;
   signal obuf2_tx         : t_fl64;
   signal obuf3_tx         : t_fl64;
   signal mi       : t_mi32;

  signal fl_sim_ctrl        : t_fl_ctrl;
  signal fl_sim_strobe      : std_logic;
  signal fl_sim_busy        : std_logic;
-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

-- ----------------------------------------------------
-- UUT mapping

   -- -------------------------------------------------------------------------
   --                    FL Simulation Components
   -- -------------------------------------------------------------------------
   fl_sim: entity work.FL_SIM
      generic map (
         DATA_WIDTH     => 64,
         FRAME_PARTS    => 1,
         RX_LOG_FILE    => "",
         TX_LOG_FILE    => ""
      )
      port map (
         -- Common interface
         FL_RESET       => reset,
         FL_CLK         => wrclk,
   
         -- Frame link Interface
         RX_DATA        => (others => '0'),
         RX_REM         => (others => '0'),
         RX_SOF_N       => '1',
         RX_EOF_N       => '1',
         RX_SOP_N       => '1',
         RX_EOP_N       => '1',
         RX_SRC_RDY_N   => '1', -- Source isn't ready
         RX_DST_RDY_N   => open,
   
         TX_DATA        => obuf0_tx.DATA,
         TX_REM         => obuf0_tx.DREM,
         TX_SOF_N       => obuf0_tx.SOF_N,
         TX_EOF_N       => obuf0_tx.EOF_N,
         TX_SOP_N       => obuf0_tx.SOP_N,
         TX_EOP_N       => obuf0_tx.EOP_N,
         TX_SRC_RDY_N   => obuf0_tx.SRC_RDY_N,
         TX_DST_RDY_N   => obuf0_tx.DST_RDY_N,
   
         -- FL SIM interface
         CTRL           => fl_sim_ctrl,
         STROBE         => fl_sim_strobe,
         BUSY           => fl_sim_busy
      );

UUT: entity work.obuf_top4_fl64
   generic map(
         DFIFO_SIZE  => 511,
         SFIFO_SIZE  => 127,
         CTRL_CMD    => false,
         INBANDFCS   => false,
         SKIP_FCS    => false
   )
   port map(

      -- ---------------- Control signal -----------------
      RESET         => reset,
      WRCLK         => wrclk,
      REFCLK        => refclk,

      -- ------------- FrameLink interface ---------------
      OBUF0_TX         => obuf0_tx,
      OBUF1_TX         => obuf1_tx,
      OBUF2_TX         => obuf2_tx,
      OBUF3_TX         => obuf3_tx,

      -- -------------- GMII/MII interface ---------------
      -- Interface 0
      OBUF0_TXCLK       => txclk,
      OBUF0_TXD         => txd,
      OBUF0_TXEN        => txen,
      OBUF0_TXER        => txer,
      -- Interface 1
      OBUF1_TXCLK      => open,
      OBUF1_TXD        => open,
      OBUF1_TXEN       => open,
      OBUF1_TXER       => open,
      -- Interface 2
      OBUF2_TXCLK      => open,
      OBUF2_TXD        => open,
      OBUF2_TXEN       => open,
      OBUF2_TXER       => open,
      -- Interface 3
      OBUF3_TXCLK      => open,
      OBUF3_TXD        => open,
      OBUF3_TXEN       => open,
      OBUF3_TXER       => open,

      -- ---------- Internal bus signals ----------------
      MI               => mi
   ); 

-- ----------------------------------------------------
-- rx_clk_gmii clock generator
txclk_clkgen : process
begin
   refclk <= '1';
   wait for gmii_clkper/2;
   refclk <= '0';
   wait for gmii_clkper/2;
end process;

-- wrclk clock generator
wrclk_clkgen : process
begin
   wrclk <= '1';
   wait for wr_clkper/2;
   wrclk <= '0';
   wait for wr_clkper/2;
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

rx_p : process

-- ----------------------------------------------------------------
--                    Procedures declaration
-- ----------------------------------------------------------------

procedure fl_op(ctrl : in t_fl_ctrl) is
begin
  wait until (WRCLK'event and wrclk='1' and fl_sim_busy = '0');
  fl_sim_ctrl <= ctrl;
  fl_sim_strobe <= '1';
  wait until (wrclk'event and wrclk='1');
  fl_sim_strobe <= '0';
end fl_op;

begin
   wait for reset_time;

   while(true) loop
      -- fl_op(fl_send32("./fl_sim_packet1.txt"));
      fl_op(fl_send32("./fl_sim_send.txt"));
   end loop;
   wait;
end process;

end architecture behavioral;
