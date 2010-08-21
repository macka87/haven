-- testbench.vhd: Network Module testbench file
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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

library work;
use work.math_pack.all;
use work.lb_pkg.all; -- Local Bus Package
use work.ib_sim_oper.all; -- Internal Bus Simulation Package
use work.fl_bfm_pkg.all;
use work.fl_bfm_rdy_pkg.all;


entity testbench is
end testbench;

architecture testbench of testbench is

constant CLKPER         : time      := 8 ns;
constant CLKPER_ETH     : time      := 6.4 ns;
constant RESET_TIME     : time      := 20 * CLKPER;

signal xgmii_reset          : std_logic_vector(  1 downto 0);
signal xgmii_rxclk          : std_logic_vector(  1 downto 0);
signal xgmii_rxd            : std_logic_vector(127 downto 0);
signal xgmii_rxc            : std_logic_vector( 15 downto 0);

signal xgmii_txclk          : std_logic_vector(  1 downto 0);
signal xgmii_txd            : std_logic_vector(127 downto 0);
signal xgmii_txc            : std_logic_vector( 15 downto 0);

signal xgmii_clk     : std_logic;
signal clk           : std_logic;
signal reset         : std_logic;

signal rx0_data      : std_logic_vector(127 downto 0);
signal rx0_drem      : std_logic_vector(3 downto 0);
signal rx0_sof_n     : std_logic;
signal rx0_eof_n     : std_logic;
signal rx0_sop_n     : std_logic;
signal rx0_eop_n     : std_logic;
signal rx0_src_rdy_n : std_logic;
signal rx0_dst_rdy_n : std_logic;

signal rx1_data      : std_logic_vector(127 downto 0);
signal rx1_drem      : std_logic_vector(3 downto 0);
signal rx1_sof_n     : std_logic;
signal rx1_eof_n     : std_logic;
signal rx1_sop_n     : std_logic;
signal rx1_eop_n     : std_logic;
signal rx1_src_rdy_n : std_logic;
signal rx1_dst_rdy_n : std_logic;

signal tx0_data      : std_logic_vector(127 downto 0);
signal tx0_drem      : std_logic_vector(3 downto 0);
signal tx0_sof_n     : std_logic;
signal tx0_eof_n     : std_logic;
signal tx0_sop_n     : std_logic;
signal tx0_eop_n     : std_logic;
signal tx0_src_rdy_n : std_logic;
signal tx0_dst_rdy_n : std_logic;

signal tx1_data      : std_logic_vector(127 downto 0);
signal tx1_drem      : std_logic_vector(3 downto 0);
signal tx1_sof_n     : std_logic;
signal tx1_eof_n     : std_logic;
signal tx1_sop_n     : std_logic;
signal tx1_eop_n     : std_logic;
signal tx1_src_rdy_n : std_logic;
signal tx1_dst_rdy_n : std_logic;

      -- PACODAG interface
signal ibuf0_ctrl_clk       : std_logic;
signal ibuf0_ctrl_reset     : std_logic;
signal ibuf0_ctrl_data      : std_logic_vector(127 downto 0);
signal ibuf0_ctrl_rem       : std_logic_vector(3 downto 0);
signal ibuf0_ctrl_src_rdy_n : std_logic;
signal ibuf0_ctrl_sop_n     : std_logic;
signal ibuf0_ctrl_eop_n     : std_logic;
signal ibuf0_ctrl_dst_rdy_n : std_logic;
signal ibuf0_ctrl_rdy       : std_logic;
      -- ibuf status interface
signal ibuf0_sop            : std_logic;
signal ibuf0_payload_len    : std_logic_vector(15 downto 0);
signal ibuf0_frame_error    : std_logic; -- 0: OK, 1: Error occured
signal ibuf0_crc_check_failed:std_logic; -- 0: OK, 1: Bad CRC 
signal ibuf0_mac_check_failed:std_logic; -- 0: OK, 1: Bad MAC
signal ibuf0_len_below_min  : std_logic; -- 0: OK, 1: Length is below min
signal ibuf0_len_over_mtu   : std_logic; -- 0: OK, 1: Length is over MTU
signal ibuf0_stat_dv        : std_logic;
      -- sampling unit interfa
signal ibuf0_sau_clk        : std_logic;
signal ibuf0_sau_reset      : std_logic;
signal ibuf0_sau_req        : std_logic;
signal ibuf0_sau_accept     : std_logic;
signal ibuf0_sau_dv         : std_logic;

      -- PACODAG interface
signal ibuf1_ctrl_clk       : std_logic;
signal ibuf1_ctrl_reset     : std_logic;
signal ibuf1_ctrl_data      : std_logic_vector(127 downto 0);
signal ibuf1_ctrl_rem       : std_logic_vector(3 downto 0);
signal ibuf1_ctrl_src_rdy_n : std_logic;
signal ibuf1_ctrl_sop_n     : std_logic;
signal ibuf1_ctrl_eop_n     : std_logic;
signal ibuf1_ctrl_dst_rdy_n : std_logic;
signal ibuf1_ctrl_rdy       : std_logic;
      -- ibuf status interface
signal ibuf1_sop            : std_logic;
signal ibuf1_payload_len    : std_logic_vector(15 downto 0);
signal ibuf1_frame_error    : std_logic; -- 0: OK, 1: Error occured
signal ibuf1_crc_check_failed:std_logic; -- 0: OK, 1: Bad CRC 
signal ibuf1_mac_check_failed:std_logic; -- 0: OK, 1: Bad MAC
signal ibuf1_len_below_min  : std_logic; -- 0: OK, 1: Length is below min
signal ibuf1_len_over_mtu   : std_logic; -- 0: OK, 1: Length is over MTU
signal ibuf1_stat_dv        : std_logic;
      -- sampling unit interfa
signal ibuf1_sau_clk        : std_logic;
signal ibuf1_sau_reset      : std_logic;
signal ibuf1_sau_req        : std_logic;
signal ibuf1_sau_accept     : std_logic;
signal ibuf1_sau_dv         : std_logic;

signal ibuf_led   : std_logic_Vector(1 downto 0);
signal obuf_led   : std_logic_Vector(1 downto 0);

      -- Local Bus interface
signal dwr        : std_logic_vector(15 downto 0);
signal be         : std_logic_vector(1 downto 0);
signal ads_n      : std_logic;
signal rd_n       : std_logic;
signal wr_n       : std_logic;
signal drd        : std_logic_vector(15 downto 0);
signal rdy_n      : std_logic;
signal err_n      : std_logic;
signal abort_n    : std_logic;

-- LB simulation signals
signal ib_sim_ctrl         : t_ib_ctrl;
signal ib_sim_strobe       : std_logic;
signal ib_sim_busy         : std_logic;

begin

uut: entity work.NETWORK_MOD_10G2
   port map(
      -- Clock signal for user interface
      USER_CLK             => clk,
      -- FrameLink reset
      FL_RESET             => reset,
      -- ICS reset,
      BUSRESET             => reset,

      -- 2 XGMII INTERFACES
      -- RX
      XGMII_RESET          => xgmii_reset,
      XGMII_RXCLK          => xgmii_rxclk,
      XGMII_RXD            => xgmii_rxd,
      XGMII_RXC            => xgmii_rxc,
      -- TX                   -- tx,
      XGMII_TXCLK          => xgmii_txclk,
      XGMII_TXD            => xgmii_txd,
      XGMII_TXC            => xgmii_txc,

      -- USER INTERFACE
      -- Network interface 
      IBUF0_TX_SOF_N       => rx0_sof_n,
      IBUF0_TX_SOP_N       => rx0_sop_n,
      IBUF0_TX_EOP_N       => rx0_eop_n,
      IBUF0_TX_EOF_N       => rx0_eof_n,
      IBUF0_TX_SRC_RDY_N   => rx0_src_rdy_n,
      IBUF0_TX_DST_RDY_N   => rx0_dst_rdy_n,
      IBUF0_TX_DATA        => rx0_data,
      IBUF0_TX_REM         => rx0_drem,

      -- PACODAG interface
      IBUF0_CTRL_CLK       => ibuf0_ctrl_clk,
      IBUF0_CTRL_RESET     => ibuf0_ctrl_reset,
      IBUF0_CTRL_DATA      => ibuf0_ctrl_data,
      IBUF0_CTRL_REM       => ibuf0_ctrl_rem,
      IBUF0_CTRL_SRC_RDY_N => ibuf0_ctrl_src_rdy_n,
      IBUF0_CTRL_SOP_N     => ibuf0_ctrl_sop_n,
      IBUF0_CTRL_EOP_N     => ibuf0_ctrl_eop_n,
      IBUF0_CTRL_DST_RDY_N => ibuf0_ctrl_dst_rdy_n,
      IBUF0_CTRL_RDY       => ibuf0_ctrl_rdy,
                                                   
      -- IBUF status interf   -- ibuf status interf
      IBUF0_SOP            => ibuf0_sop,
      IBUF0_PAYLOAD_LEN    => ibuf0_payload_len,
      IBUF0_FRAME_ERROR    => ibuf0_frame_error,
      IBUF0_CRC_CHECK_FAILED=>ibuf0_crc_check_failed,
      IBUF0_MAC_CHECK_FAILED=>ibuf0_mac_check_failed,
      IBUF0_LEN_BELOW_MIN  => ibuf0_len_below_min,
      IBUF0_LEN_OVER_MTU   => ibuf0_len_over_mtu,
      IBUF0_STAT_DV        => ibuf0_stat_dv,
                                                   
      -- Sampling unit interfa-- sampling unit intece
      IBUF0_SAU_CLK        => ibuf0_sau_clk,
      IBUF0_SAU_RESET      => ibuf0_sau_reset,
      IBUF0_SAU_REQ        => ibuf0_sau_req,
      IBUF0_SAU_ACCEPT     => ibuf0_sau_accept,
      IBUF0_SAU_DV         => ibuf0_sau_dv,
      
      -- Output buffer inte
      OBUF0_RX_SOF_N       => tx0_sof_n,
      OBUF0_RX_SOP_N       => tx0_sop_n,
      OBUF0_RX_EOP_N       => tx0_eop_n,
      OBUF0_RX_EOF_N       => tx0_eof_n,
      OBUF0_RX_SRC_RDY_N   => tx0_src_rdy_n,
      OBUF0_RX_DST_RDY_N   => tx0_dst_rdy_n,
      OBUF0_RX_DATA        => tx0_data,
      OBUF0_RX_REM         => tx0_drem,
      
      -- Network interface 
      IBUF1_TX_SOF_N       => rx1_sof_n,
      IBUF1_TX_SOP_N       => rx1_sop_n,
      IBUF1_TX_EOP_N       => rx1_eop_n,
      IBUF1_TX_EOF_N       => rx1_eof_n,
      IBUF1_TX_SRC_RDY_N   => rx1_src_rdy_n,
      IBUF1_TX_DST_RDY_N   => rx1_dst_rdy_n,
      IBUF1_TX_DATA        => rx1_data,
      IBUF1_TX_REM         => rx1_drem,
                                                      
      -- PACODAG interface                            
      IBUF1_CTRL_CLK       => ibuf1_ctrl_clk,
      IBUF1_CTRL_RESET     => ibuf1_ctrl_reset,
      IBUF1_CTRL_DATA      => ibuf1_ctrl_data,
      IBUF1_CTRL_REM       => ibuf1_ctrl_rem,
      IBUF1_CTRL_SRC_RDY_N => ibuf1_ctrl_src_rdy_n,
      IBUF1_CTRL_SOP_N     => ibuf1_ctrl_sop_n,
      IBUF1_CTRL_EOP_N     => ibuf1_ctrl_eop_n,
      IBUF1_CTRL_DST_RDY_N => ibuf1_ctrl_dst_rdy_n,
      IBUF1_CTRL_RDY       => ibuf1_ctrl_rdy,
                                                   
      -- IBUF status interf   -- ibuf status interf
      IBUF1_SOP            => ibuf1_sop,
      IBUF1_PAYLOAD_LEN    => ibuf1_payload_len,
      IBUF1_FRAME_ERROR    => ibuf1_frame_error,
      IBUF1_CRC_CHECK_FAILED=>ibuf1_crc_check_failed,
      IBUF1_MAC_CHECK_FAILED=>ibuf1_mac_check_failed,
      IBUF1_LEN_BELOW_MIN  => ibuf1_len_below_min,
      IBUF1_LEN_OVER_MTU   => ibuf1_len_over_mtu,
      IBUF1_STAT_DV        => ibuf1_stat_dv,
                                                   
      -- Sampling unit inte   -- sampling unit intece
      IBUF1_SAU_CLK        => ibuf1_sau_clk,
      IBUF1_SAU_RESET      => ibuf1_sau_reset,
      IBUF1_SAU_REQ        => ibuf1_sau_req,
      IBUF1_SAU_ACCEPT     => ibuf1_sau_accept,
      IBUF1_SAU_DV         => ibuf1_sau_dv,
                                                      
      -- Output buffer inte                           
      OBUF1_RX_SOF_N       => tx1_sof_n,
      OBUF1_RX_SOP_N       => tx1_sop_n,
      OBUF1_RX_EOP_N       => tx1_eop_n,
      OBUF1_RX_EOF_N       => tx1_eof_n,
      OBUF1_RX_SRC_RDY_N   => tx1_src_rdy_n,
      OBUF1_RX_DST_RDY_N   => tx1_dst_rdy_n,
      OBUF1_RX_DATA        => tx1_data,
      OBUF1_RX_REM         => tx1_drem,

      -- Led interface
      IBUF_LED             => ibuf_led,
      OBUF_LED             => obuf_led,
      
      -- Local Bus interfac
      LOCAL_BUS_DWR        => dwr,
      LOCAL_BUS_BE         => be,
      LOCAL_BUS_ADS_N      => ads_n,
      LOCAL_BUS_RD_N       => rd_n,
      LOCAL_BUS_WR_N       => wr_n,
      LOCAL_BUS_DRD        => drd,
      LOCAL_BUS_RDY_N      => rdy_n,
      LOCAL_BUS_ERR_N      => err_n,
      LOCAL_BUS_ABORT_N    => abort_n
   );

MI32_SIM_U : entity work.LB_SIM
   generic map (
      UPSTREAM_LOG_FILE   => "ib_upstream_log.txt",
      DOWNSTREAM_LOG_FILE => "ib_downstream_log.txt",
      BASE_ADDR           => X"00001000",
      LIMIT               => X"00003000"
   )
   port map (
      -- Common interface
      RESET           => reset,
      CLK             => clk,

      -- LocalBus Interface
      DWR        => dwr,
      BE         => be,
      ADS_N      => ads_n,
      RD_N       => rd_n,
      WR_N       => wr_n,
      DRD        => drd,
      RDY_N      => rdy_n,
      ERR_N      => err_n,
      ABORT_N    => abort_n,

      -- IB SIM interface
      CTRL               => ib_sim_ctrl,
      STROBE             => ib_sim_strobe,
      BUSY               => ib_sim_busy
   );

   FL_BFM_U : entity work.FL_BFM
   generic map (
      DATA_WIDTH  => 128,
      FL_BFM_ID   => 0
   )
   port map (
      -- Common interface
      RESET       => reset,
      CLK         => clk,

      TX_DATA     => tx0_data,
      TX_REM      => tx0_drem,
      TX_SOF_N    => tx0_sof_n,
      TX_EOF_N    => tx0_eof_n,
      TX_SOP_N    => tx0_sop_n,
      TX_EOP_N    => tx0_eop_n,
      TX_SRC_RDY_N=> tx0_src_rdy_n,
      TX_DST_RDY_N=> tx0_dst_rdy_n
   );

clkgen: process
begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
end process;

xgmii_clkgen: process
begin
   xgmii_clk <= '1';
   wait for clkper_eth/2;
   xgmii_clk <= '0';
   wait for clkper_eth/2;
end process;

xgmii_rxclk <= xgmii_clk & xgmii_clk;
xgmii_txclk <= xgmii_clk & xgmii_clk;

reset_gen : process
begin
   RESET <= '1';
   wait for RESET_TIME;
   wait for 1 ns;
   RESET <= '0';
   wait;
end process reset_gen;

xgmii_reset <= reset & reset;

tb: process

-- Support for ib_op
procedure ib_op(ctrl : in t_ib_ctrl) is
begin
   wait until (CLK'event and CLK='1' and ib_sim_busy = '0');
   ib_sim_ctrl <= ctrl;
   ib_sim_strobe <= '1';
   wait until (CLK'event and CLK='1');
   ib_sim_strobe <= '0';
end ib_op;

begin

   wait for 2*reset_time;

   -- Enable OBUF0
   ib_op(ib_local_write(X"00002020",   -- dst addr
                        X"00000000",   -- src addr
                        4,             -- length
                        16#ABAB#,      -- tag
                        '0',           -- No completition ack
                        X"0000000000000001")); -- data

   wait for 20*clkper;
   wait for 1 ns;

   -- 10 packets 60 B long (4 B of CRC added in OBUF)
   SendWriteFile("packet_64B.txt", EVER, flCmd_0,16#0#);

   SendWriteFile("packet_1518B.txt", EVER, flCmd_0,16#0#);
   SendWriteFile("packet_1518B.txt", EVER, flCmd_0,16#0#);
   SendWriteFile("packet_1518B.txt", EVER, flCmd_0,16#0#);
   SendWriteFile("packet_1518B.txt", EVER, flCmd_0,16#0#);

   -- 10 packets 60 B long (4 B of CRC added in OBUF)
   SendWriteFile("packet_64B.txt", EVER, flCmd_0,16#0#);

   wait;
   end process;

end;
