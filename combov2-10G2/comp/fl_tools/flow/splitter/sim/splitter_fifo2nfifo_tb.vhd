--
-- splitter_fifo2nfifo_tb.vhd: Testbench for FrameLink Splitter
-- Copyright (C) 2009 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--            Jakub Olbert <xolber00@stud.fit.vutbr.cz>
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
--
-- TODO:
--
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;
use work.math_pack.all;

-- Framelink simulation
use work.fl_sim_oper.all;
use work.fl_bfm_rdy_pkg.all;
use work.FL_BFM_PKG.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant TEST_WIDTH  : integer   := 64;
   constant TEST_COUNT  : integer   := 4;
   constant FRAME_PARTS : integer   := 2;
   
   constant clkper      : time      := 10 ns;
   constant reset_time  : time      := 20 * clkper;

   -- FL_SIM constants
   constant FL_SEND_FILE  : string := "./tests/fl_input.txt";
   constant FL_RECV_FILE  : string := "./tests/fl_out";
   constant tx_rdy_driver : RDYSignalDriver := RND; -- EVER, ONOFF, RND
   constant rx_rdy_driver : RDYSignalDriver := RND;

   -- ------------------ Signals declaration ----------------------------------
   signal clk            : std_logic;
   signal reset          : std_logic;
   -- input interface
   signal rx_sof_n       : std_logic;
   signal rx_sop_n       : std_logic;
   signal rx_eop_n       : std_logic;
   signal rx_eof_n       : std_logic;
   signal rx_src_rdy_n   : std_logic;
   signal rx_dst_rdy_n   : std_logic;
   signal rx_data        : std_logic_vector(TEST_WIDTH-1 downto 0);
   signal rx_rem         : std_logic_vector(log2(TEST_WIDTH/8)-1 downto 0);
   -- output interface
   signal tx_sof_n       : std_logic_vector(TEST_COUNT-1 downto 0);
   signal tx_sop_n       : std_logic_vector(TEST_COUNT-1 downto 0);
   signal tx_eop_n       : std_logic_vector(TEST_COUNT-1 downto 0);
   signal tx_eof_n       : std_logic_vector(TEST_COUNT-1 downto 0);
   signal tx_src_rdy_n   : std_logic_vector(TEST_COUNT-1 downto 0);
   signal tx_dst_rdy_n   : std_logic_vector(TEST_COUNT-1 downto 0);
   signal tx_data        : std_logic_vector(TEST_WIDTH-1 downto 0);
   signal tx_rem         : std_logic_vector(TEST_COUNT*log2(
                                        TEST_WIDTH/TEST_COUNT/8)-1 downto 0);

   -- FL_SIM ctrl signals
   signal fl_sim_tx_ctrl   : t_fl_ctrl;
   signal fl_sim_tx_strobe : std_logic;
   signal fl_sim_tx_busy   : std_logic;
   signal fl_sim_rx_ctrl   : t_fl_ctrl;
   signal fl_sim_rx_strobe : std_logic;
   signal fl_sim_rx_busy   : std_logic;

   -- Convert integer to string (only in range 0 - 15)
   function str(int : integer) return string is
      variable s : string(1 to 1);
   begin
      case int is
         when 0 => s := "0";
         when 1 => s := "1";
         when 2 => s := "2";
         when 3 => s := "3";
         when 4 => s := "4";
         when 5 => s := "5";
         when 6 => s := "6";
         when 7 => s := "7";
         when 8 => s := "8";
         when 9 => s := "9";
         when 10 => s := "A";
         when 11 => s := "B";
         when 12 => s := "C";
         when 13 => s := "D";
         when 14 => s := "E";
         when 15 => s := "F";
         when others =>
            assert false report "str(integer): Integer is out of range!" 
               severity error;
      end case;
      return s;
   end function str;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- Framelink transmitter
   FL_TRANSMMITER : entity work.FL_BFM
      generic map(
         DATA_WIDTH => TEST_WIDTH,
         FL_BFM_ID  => 0
      )
      port map(
         -- common interface
         CLK   => CLK,
         RESET => RESET,

         -- framelink bus
         TX_DATA      => rx_data,
         TX_REM       => rx_rem,
         TX_SOF_N     => rx_sof_n,
         TX_SOP_N     => rx_sop_n,
         TX_EOP_N     => rx_eop_n,
         TX_EOF_N     => rx_eof_n,
         TX_SRC_RDY_N => rx_src_rdy_n,
         TX_DST_RDY_N => rx_dst_rdy_n
      );

   -- Generate Framelink receivers
   FL_RECEIVERS : FOR n IN 0 TO TEST_COUNT-1 GENERATE 
      FL_RECEIVER : entity work.MONITOR
         generic map(
            RX_TX_DATA_WIDTH => TEST_WIDTH/TEST_COUNT,
            FILE_NAME        => FL_RECV_FILE & str(n) & ".txt",
            FRAME_PARTS      => FRAME_PARTS,
            RDY_DRIVER       => rx_rdy_driver
         )
         port map(
            FL_CLK       => CLK,
            FL_RESET     => RESET,

            RX_DATA      => tx_data((n+1)*(TEST_WIDTH/TEST_COUNT)-1 downto
                            n*(TEST_WIDTH/TEST_COUNT)),
            RX_REM       => tx_rem((n+1)*log2(TEST_WIDTH/TEST_COUNT/8)-1 downto
                            n*log2(TEST_WIDTH/TEST_COUNT/8)),
            RX_SOF_N     => tx_sof_n(n),
            RX_SOP_N     => tx_sop_n(n),
            RX_EOF_N     => tx_eof_n(n),
            RX_EOP_N     => tx_eop_n(n),
            RX_SRC_RDY_N => tx_src_rdy_n(n),
            RX_DST_RDY_N => tx_dst_rdy_n(n)
         );
   END GENERATE FL_RECEIVERS;


-- ----------------------------------------------------
-- CLK clock generator
clkgen : process
begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
end process;

-- generate RESET signal
resetgen : process
begin
   reset <= '1';
   wait for reset_time;
   reset <= '0';
   wait;
end process;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb : process
   -- support procedure for simulation components
   procedure fl_op_tx(ctrl_tx : in t_fl_ctrl) is
   begin
      wait until (CLK'EVENT AND CLK = '1' AND fl_sim_tx_busy = '0');
      fl_sim_tx_ctrl <= ctrl_tx;
      fl_sim_tx_strobe <= '1';
      wait until (CLK'event and CLK = '1');
      fl_sim_tx_strobe <= '0';
   end procedure fl_op_tx;

begin  -- tb process
   fl_sim_tx_strobe <= '0';

   wait for reset_time;

   SetSeed(897657);
   SendWriteFile(FL_SEND_FILE, tx_rdy_driver, flCmd_0, 0);
   wait;
end process tb;

   uut : entity work.FL_SPLITTER_FIFO2NFIFO
      generic map(
         DATA_WIDTH     => TEST_WIDTH,
         OUTPUT_COUNT   => TEST_COUNT,
         FRAME_PARTS    => FRAME_PARTS
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- input interface
         RX_SOF_N       => rx_sof_n,
         RX_SOP_N       => rx_sop_n,
         RX_EOP_N       => rx_eop_n,
         RX_EOF_N       => rx_eof_n,
         RX_SRC_RDY_N   => rx_src_rdy_n,
         RX_DST_RDY_N   => rx_dst_rdy_n,
         RX_DATA        => rx_data,
         RX_REM         => rx_rem,
         -- output interace
         TX_SOF_N       => tx_sof_n,
         TX_SOP_N       => tx_sop_n,
         TX_EOP_N       => tx_eop_n,
         TX_EOF_N       => tx_eof_n,
         TX_SRC_RDY_N   => tx_src_rdy_n,
         TX_DST_RDY_N   => tx_dst_rdy_n,
         TX_DATA        => tx_data,
         TX_REM         => tx_rem
      );

end architecture behavioral;

