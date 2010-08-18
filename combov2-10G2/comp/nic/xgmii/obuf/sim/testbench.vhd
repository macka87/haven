-- testbench.vhd: Testbench for XGMII_OBUF
-- Copyright (C) 2008 CESNET
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
use work.fifo_pkg.all;
use work.math_pack.all;

use work.lb_pkg.all;
use work.ib_sim_oper.all;

-- FrameLink Simulation Package
use work.fl_sim_oper.all;
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

   -- Simulation parameters
   constant FL_WIDTH       : integer := 128;
   constant CTRL_CMD       : boolean := true;
   constant DFIFO_SIZE     : integer := 1024;
   constant HFIFO_SIZE     : integer := 256;
   constant HFIFO_MEMTYPE  : mem_type := LUT;
   constant FLBFM_BEHAVIOR : RDYSignalDriver := EVER; -- EVER, ONOFF, RND

   -- Global Constant Declaration
   constant clkper       : time := 20 ns;
   constant miclkper     : time := 10 ns;
   constant clkper_fl    : time := 10 ns;
   constant clkper_base  : time := 20 ns;
   constant clkper_xgmii : time := 6.4 ns;

   constant RESET_DELAY    : time := 1 us;

   constant END_DELAY      : time := 10 us;

   constant FRAME_PARTS    : integer := 2;

   -- Signal declaration
   signal reset         : std_logic;
   signal clk_base      : std_logic;
   signal xgmii_clk     : std_logic;
   signal mi_clk        : std_logic;
   signal fl_clk        : std_logic;

   -- xgmii interface signals
   signal xgmii_txclk       : std_logic;
   signal xgmii_txd         : std_logic_vector(31 downto 0);
   signal xgmii_txc         : std_logic_vector(3 downto 0);


   -- obuf signals
   signal obuf_rx_data       : std_logic_vector(FL_WIDTH-1 downto 0);
   signal obuf_rx_drem       : std_logic_vector(log2(FL_WIDTH/8)-1 downto 0);
   signal obuf_rx_sof_n      : std_logic;
   signal obuf_rx_eof_n      : std_logic;
   signal obuf_rx_sop_n      : std_logic;
   signal obuf_rx_eop_n      : std_logic;
   signal obuf_rx_src_rdy_n  : std_logic;
   signal obuf_rx_dst_rdy_n  : std_logic;

   signal mi                 :t_mi32;



   -- MI32 Sim signals
   signal mi32_sim_ctrl        : t_ib_ctrl;
   signal mi32_sim_strobe      : std_logic;
   signal mi32_sim_busy        : std_logic;

   -- FL Sim TX signals
   signal flsim_tx_data       : std_logic_vector(FL_WIDTH-1 downto 0);
   signal flsim_tx_drem       : std_logic_vector(log2(FL_WIDTH/8)-1 downto 0);
   signal flsim_tx_sof_n      : std_logic;
   signal flsim_tx_eof_n      : std_logic;
   signal flsim_tx_sop_n      : std_logic;
   signal flsim_tx_eop_n      : std_logic;
   signal flsim_tx_src_rdy_n  : std_logic;
   signal flsim_tx_dst_rdy_n  : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- -------------------------------------------------------------------------
   --                         OBUF
   -- -------------------------------------------------------------------------
   uut: entity work.obuf_xgmii
      generic map(
         -- Frames contain control part
         CTRL_CMD          => CTRL_CMD,
         -- FrameLink width
         FL_WIDTH_RX       => FL_WIDTH,
         -- Number of items in Data FIFO (FL_WIDTH_RX + control signals wide).
         -- !!!!!!!!!!! Must be 2^n, n>=2 !!!!!!!!!!!!!!!!!!!!!!
         DFIFO_SIZE        => DFIFO_SIZE,
         -- HFIFO item count (1-bit wide)
         HFIFO_SIZE        => HFIFO_SIZE,
         -- Type of memory used by HFIFO
         HFIFO_MEMTYPE     => HFIFO_MEMTYPE
      )
      port map(
         -- Common signals
         -- Global reset
         RESET             => reset,

         -- XGMII interface
         -- XGMII Transmit Clock
         XGMII_TXCLK       => xgmii_txclk,
         -- XGMII Transmit Data
         XGMII_TXD         => xgmii_txd,
         -- XGMII Transmit Control
         XGMII_TXC         => xgmii_txc,
         -- Reference Transmit Clock provided by user (156.25MHz)
         TX_CLK_REF        => xgmii_clk,

         -- Input FrameLink inteface
         RX_SOF_N          => obuf_rx_sof_n,
         RX_SOP_N          => obuf_rx_sop_n,
         RX_EOP_N          => obuf_rx_eop_n,
         RX_EOF_N          => obuf_rx_eof_n,
         RX_SRC_RDY_N      => obuf_rx_src_rdy_n,
         RX_DST_RDY_N      => obuf_rx_dst_rdy_n,
         RX_DATA           => obuf_rx_data,
         RX_REM            => obuf_rx_drem,
         -- Clock for FrameLink interface.
         FL_CLK            => fl_clk,

         -- MI32 interface
         MI                => mi,
         -- Clock for MI32 interface
         MI_CLK            => mi_clk
      );

   -- -------------------------------------------------------------------------
   --                   MI32 Simulation Component
   -- -------------------------------------------------------------------------
   mi32_sim: entity work.mi32_sim
      generic map (
         UPSTREAM_LOG_FILE   => "./mi32.upstream",
         DOWNSTREAM_LOG_FILE => "./mi32.downstream",
         BASE_ADDR           => X"00000000",
         LIMIT               => X"00000100",
         FREQUENCY           => LOCAL_BUS_FREQUENCY,
         BUFFER_EN           => false
      )
      port map (
         -- Common interface
         IB_RESET            => reset,
         IB_CLK              => mi_clk,

         -- User Component Interface
         CLK                 => mi_clk,
         MI32                => mi,

         -- IB SIM interface
         STATUS              => open,
         CTRL                => mi32_sim_ctrl,
         STROBE              => mi32_sim_strobe,
         BUSY                => mi32_sim_busy
     );


   -- -------------------------------------------------------------------------
   --                   FL Simulation Component - TX
   -- -------------------------------------------------------------------------
   fl_sim_tx: entity work.FL_BFM
      generic map (
         DATA_WIDTH     => FL_WIDTH,
         FL_BFM_ID      => 0
      )
      port map (
         -- Common interface
         RESET          => reset,
         CLK            => fl_clk,

         TX_DATA        => flsim_tx_data,
         TX_REM         => flsim_tx_drem,
         TX_SOF_N       => flsim_tx_sof_n,
         TX_EOF_N       => flsim_tx_eof_n,
         TX_SOP_N       => flsim_tx_sop_n,
         TX_EOP_N       => flsim_tx_eop_n,
         TX_SRC_RDY_N   => flsim_tx_src_rdy_n,
         TX_DST_RDY_N   => flsim_tx_dst_rdy_n
      );



   -- -------------------------------------------------------------------------
   --                   FL TRIM
   -- -------------------------------------------------------------------------
   fl_trim_gen: if CTRL_CMD = false generate
   begin
     fl_trimmer: entity work.FL_TRIMMER
         generic map(
            DATA_WIDTH     => FL_WIDTH,
            -- information about frame --
            -- header is present in frame
            HEADER         => false,
            -- footer is present in frame
            FOOTER         => true,
            -- if true, header is trimmed
            TRIM_HEADER    => false,
            -- if true, footer is trimmed
            TRIM_FOOTER    => true
         )
         port map(
            CLK            => fl_clk,
            RESET          => reset,

            -- input interface
            RX_SOF_N       => flsim_tx_sof_n,
            RX_SOP_N       => flsim_tx_sop_n,
            RX_EOP_N       => flsim_tx_eop_n,
            RX_EOF_N       => flsim_tx_eof_n,
            RX_SRC_RDY_N   => flsim_tx_src_rdy_n,
            RX_DST_RDY_N   => flsim_tx_dst_rdy_n,
            RX_DATA        => flsim_tx_data,
            RX_REM         => flsim_tx_drem,

            -- output interface
            TX_SOF_N       => obuf_rx_sof_n,
            TX_SOP_N       => obuf_rx_sop_n,
            TX_EOP_N       => obuf_rx_eop_n,
            TX_EOF_N       => obuf_rx_eof_n,
            TX_SRC_RDY_N   => obuf_rx_src_rdy_n,
            TX_DST_RDY_N   => obuf_rx_dst_rdy_n,
            TX_DATA        => obuf_rx_data,
            TX_REM         => obuf_rx_drem,

            -- control signals
            ENABLE         => '1'
         );
   end generate fl_trim_gen;

   not_fl_trim_gen: if CTRL_CMD = true generate
   begin
      flsim_tx_dst_rdy_n <= obuf_rx_dst_rdy_n;
      obuf_rx_data       <= flsim_tx_data;
      obuf_rx_drem       <= flsim_tx_drem;
      obuf_rx_sop_n      <= flsim_tx_sop_n;
      obuf_rx_sof_n      <= flsim_tx_sof_n;
      obuf_rx_eop_n      <= flsim_tx_eop_n;
      obuf_rx_eof_n      <= flsim_tx_eof_n;
      obuf_rx_src_rdy_n  <= flsim_tx_src_rdy_n;
   end generate not_fl_trim_gen;



   -- ----------------------------------------------------
   -- CLK_BASE clock generator
   clkgen_base : process
   begin
      clk_base <= '1';
      wait for clkper_base/2;
      clk_base <= '0';
      wait for clkper_base/2;
   end process;

   -- ----------------------------------------------------
   -- MI clock generator
   clkgen_mi : process
   begin
      mi_clk <= '1';
      wait for miclkper/2;
      mi_clk <= '0';
      wait for miclkper/2;
   end process;

   -- ----------------------------------------------------
   -- XGMII clock generator
   clkgen_xgmii : process
   begin
      xgmii_clk <= '1';
      wait for clkper_xgmii/2;
      xgmii_clk <= '0';
      wait for clkper_xgmii/2;
   end process;

   -- ----------------------------------------------------
   -- FL clock generator
   clkgen_fl : process
   begin
      fl_clk <= '1';
      wait for clkper_fl/2;
      fl_clk <= '0';
      wait for clkper_fl/2;
   end process;

   -- ----------------------------------------------------
   -- Reset generation
   proc_reset : process
   begin
      reset <= '1';
      wait for RESET_DELAY;
      reset <= '0';
      wait;
   end process;


   -- ----------------------------------------------------------------------------
   --                         Main testbench process
   -- ----------------------------------------------------------------------------

   tb : process
      -- ----------------------------------------------------------------
      --                    Procedures declaration
      -- ----------------------------------------------------------------

      -- This procedure must be placed in this testbench file. Using this
      -- procedure is necessary for correct function of MI32_SIM
      procedure ib_op(ctrl : in t_ib_ctrl) is
      begin
         wait until (mi_clk'event and mi_clk='1' and mi32_sim_busy = '0');
         mi32_sim_ctrl <= ctrl;
         mi32_sim_strobe <= '1';
         wait until (mi_clk'event and mi_clk='1');
         mi32_sim_strobe <= '0';
      end ib_op;


   -- ----------------------------------------------------------------
   --                        Testbench Body
   -- ----------------------------------------------------------------
   begin

      wait for 2*RESET_DELAY;

      -- MAC address inicialization
      ib_op(ib_local_write(X"00000024", X"11111111", 1, 16#ABAB#, '0', X"0000000011C9180A"));
      ib_op(ib_local_write(X"00000028", X"11111111", 1, 16#ABAB#, '0', X"0000000000010009"));

      -- Enable OBUF
      ib_op(ib_local_write(X"00000020", X"11111111", 1, 16#ABAB#, '0', X"0000000000000001"));

      wait for 10*clkper;

      -- Start transmission of FL frames
      SendWriteFile("./fl_sim_send.txt", FLBFM_BEHAVIOR, flCmd_0, 0);

      wait for 10*clkper;

      wait for END_DELAY;

      wait;
   end process;

end architecture behavioral;
