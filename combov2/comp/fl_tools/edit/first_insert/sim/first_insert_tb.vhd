-- first_insert_tb.vhd: Testbench for First insert unit
-- Copyright (C) 2008 CESNET
-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
use work.fl_pkg.all;
use work.fl_bfm_pkg.all;
use work.fl_bfm_rdy_pkg.all; 



-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;



-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

-- -----------------------Testbench constant-----------------------------------
   constant clkper_50       : time    := 20 ns;
   constant clkper_100      : time    := 10 ns;
   constant reset_time      : time    := 100 * clkper_100;

   constant DATA_WIDTH      : integer := 64;

-- -----------------------Testbench auxilarity signals-------------------------
   -- CLK_GEN Signals
   signal reset     : std_logic;
   signal clk       : std_logic;
   signal clk_50_in : std_logic;
   signal clk50     : std_logic;
   signal clk100    : std_logic;
   signal lock      : std_logic;

   -- Frame Link Bus 128 (input)
   signal RX       : t_fl64;
     
   -- Frame Link Bus 128 (input)
   signal TX       : t_fl64;

   

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
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

   -- -------------------------------------------------------------------------
   --                   Header REARRANGER
   -- -------------------------------------------------------------------------
   uut: entity work.FL_FIRST_INSERT
      port map (
         CLK               => CLK,
         RESET             => RESET,
	 DATA              => X"0011223344556677",

         RX_DATA           => RX.DATA,
         RX_REM            => RX.DREM,
         RX_SOF_N          => RX.SOF_N,
         RX_SOP_N          => RX.SOP_N,
         RX_EOP_N          => RX.EOP_N,
         RX_EOF_N          => RX.EOF_N,
         RX_SRC_RDY_N      => RX.SRC_RDY_N,
         RX_DST_RDY_N      => RX.DST_RDY_N,

         TX_DATA           => TX.DATA,
         TX_REM            => TX.DREM,
         TX_SOF_N          => TX.SOF_N,
         TX_SOP_N          => TX.SOP_N,
         TX_EOP_N          => TX.EOP_N,
         TX_EOF_N          => TX.EOF_N,
         TX_SRC_RDY_N      => TX.SRC_RDY_N,
         TX_DST_RDY_N      => TX.DST_RDY_N
      );

   -- FL_BFM component for input interface -------------------------------------
   FL_BFM_RX_U : entity work.FL_BFM
   generic map (
      DATA_WIDTH   => DATA_WIDTH,
      FL_BFM_ID    => 0
   )
   port map (
      -- Common interface
      RESET        => reset,
      CLK          => clk,

      TX_DATA      => RX.DATA,
      TX_REM       => RX.DREM,
      TX_SOF_N     => RX.SOF_N,
      TX_EOF_N     => RX.EOF_N,
      TX_SOP_N     => RX.SOP_N,
      TX_EOP_N     => RX.EOP_N,
      TX_SRC_RDY_N => RX.SRC_RDY_N,
      TX_DST_RDY_N => RX.DST_RDY_N
     );
   
   -- MONITOR component for output interface -----------------------------------
   MONITOR_TX_U: entity work.MONITOR
   generic map(
      -- FrameLink data bus width
      -- only 8, 16, 32, 64 and 128 bit fl bus supported
      RX_TX_DATA_WIDTH => DATA_WIDTH,
      FILE_NAME        => "./tests/monitor_tx.txt",
      FRAME_PARTS      => 2,
      RDY_DRIVER       => RND
   )
   port map(
      -- Common interface
      FL_RESET     => reset,
      FL_CLK       => clk,

      -- RX Frame link Interface
      RX_DATA      => TX.DATA,
      RX_REM       => TX.DREM,
      RX_SOF_N     => TX.SOF_N,
      RX_EOF_N     => TX.EOF_N,
      RX_SOP_N     => TX.SOP_N,
      RX_EOP_N     => TX.EOP_N,
      RX_SRC_RDY_N => TX.SRC_RDY_N,
      RX_DST_RDY_N => TX.DST_RDY_N      
     );
     
   tb : process
   begin
      -- set seed for random generator
      SetSeed(6566);

      -- wait for reset time
      wait for reset_time;

      -- send fl transactions to input interfaces of crossbar
      SendWriteFile("./tests/sim_rx.txt", RND, flCmd_0, 0);
   end process;
end architecture behavioral;
