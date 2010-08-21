-- marker_tb.vhd: FrameLink Marker testbench.
-- Copyright (C) 2006 CESNET
-- Author(s): Adam Crha <xcrhaa00@liberouter.org>
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

use std.textio.all;
use work.fl_pkg.all;
use work.fl_sim_oper.all;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

use work.math_pack.all;
use work.lb_pkg.all;
use work.ib_sim_oper.all; -- MI32 Simulation Package

-- FL BFM and monitor packages
use work.fl_sim_oper.all;
use work.fl_bfm_rdy_pkg.all;
use work.FL_BFM_pkg.all;

-- Libraries needed to fix broken MI32 sim
use std.textio.all;
use IEEE.std_logic_textio.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture testbench_arch of testbench is
   -- Global Constant Declaration

   constant RESET_DELAY : time := 1 us;

   constant INFINITE_PCKTS : boolean := false;
   constant FLBFM_BEHAVIOR : RDYSignalDriver := RND; -- EVER, ONOFF, RND
   constant FLMONITOR_BEHAVIOR : RDYSignalDriver := RND; -- EVER, ONOFF, RND


   constant FLSIM_SEND_FILE : string := "./fl_sim_send.txt";

   -- uut configuration
   constant clkper_base   : time := 10 ns;
   constant reset_time  : time := 1 us;
   --constant RX_LOG      : string :="";
   --constant TX_LOG      : string :="./data/fl_sim_tx.txt";
   --constant OFFSET    : integer := 3;
   constant FL_WIDTH  : integer := 16; --
   constant FRAME_LEN   : integer := 15; --Lenght of frame in bits 
   --constant WORDCOUNT   : integer := DATA_WIDTH/FRAME_LEN; --number of wires
   constant WORDCOUNT   : integer := FRAME_LEN; --number of wires
   constant FRAME_PARTS : integer := 1;

-- -----------------------Testbench auxilarity signals-------------------------
   -- CLK_GEN Signals
   signal reset               : std_logic;
   signal non_reset           : std_logic; 
   signal clk                 : std_logic;
   signal clk_base            : std_logic;
 
   signal fl_clk              : std_logic;
   signal reset_value         : std_logic_vector(FRAME_LEN*FL_WIDTH-1 downto 0);--edit
   --  input interface
   signal rx_sof_n       : std_logic;
   signal rx_sop_n       : std_logic;
   signal rx_eop_n       : std_logic;
   signal rx_eof_n       : std_logic;
   signal rx_src_rdy_n   : std_logic;
   signal rx_dst_rdy_n   : std_logic;
   signal rx_data        : std_logic_vector(FL_WIDTH-1 downto 0);
   signal rx_rem         : std_logic_vector(log2(FL_WIDTH/8)-1 downto 0);

   --  output interface
   signal tx_sof_n       : std_logic;
   signal tx_sop_n       : std_logic;
   signal tx_eop_n       : std_logic;
   signal tx_eof_n       : std_logic;
   signal tx_src_rdy_n   : std_logic;
   signal tx_dst_rdy_n   : std_logic;
   signal tx_data        : std_logic_vector(FL_WIDTH-1 downto 0);
   signal tx_rem         : std_logic_vector(log2(FL_WIDTH/8)-1 downto 0);

   -- MI32 interface
   signal mi             : t_mi32;

   -- MI32 Sim signals
   signal mi32_sim_ctrl        : t_ib_ctrl;
   signal mi32_sim_strobe      : std_logic;
   signal mi32_sim_busy        : std_logic;


  
-- ----------------------------------------------------------------------------
--                      Architecture body
      
-- ----------------------------------------------------------------------------
begin

   -- Reset value is set to zeroes (TODO, try to change the value or even make
   -- a process and reset the component more than once)
   reset_value <= (others => '1');

   -- ----------------------------------------------------
   -- Reset generation
   reset_gen : process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process reset_gen;
   non_reset <= not reset;


   -- ----------------------------------------------------
   -- CLK_BASE clock generator
   clkgen_base : process
   begin
      clk_base <= '1';
      wait for clkper_base/2;
      clk_base <= '0';
      wait for clkper_base/2;
   end process;
   clk <= clk_base;
   fl_clk <= clk;

   -- ----------------------------------------------------
   -- FL simulator
   UUT: entity work.fl_masker
   generic map (
      FL_WIDTH     => FL_WIDTH,
      FRAME_LEN    => FRAME_LEN
   )
   port map (
      CLK          => fl_clk,
      RESET        => reset,
      -- Write interface
      RX_DATA      => rx_data,
      RX_REM       => rx_rem,
      RX_SOF_N     => rx_sof_n,
      RX_EOF_N     => rx_eof_n,
      RX_SOP_N     => rx_sop_n,
      RX_EOP_N     => rx_eop_n,
      RX_SRC_RDY_N => rx_src_rdy_n,
      RX_DST_RDY_N => rx_dst_rdy_n,
      -- Read interface
      TX_DATA      => tx_data,
      TX_REM       => tx_rem,
      TX_SOF_N     => tx_sof_n,
      TX_EOF_N     => tx_eof_n,
      TX_SOP_N     => tx_sop_n,
      TX_EOP_N     => tx_eop_n,
      TX_SRC_RDY_N => tx_src_rdy_n,
      TX_DST_RDY_N => tx_dst_rdy_n,
      RESET_VALUE    => reset_value,

      -- MI32 interface
      MI32_DWR            => mi.DWR,
      MI32_ADDR           => mi.ADDR,
      MI32_RD             => mi.RD,
      MI32_WR             => mi.WR,
      MI32_BE             => mi.BE,
      MI32_DRD            => mi.DRD,
      MI32_ARDY           => mi.ARDY,
      MI32_DRDY           => mi.DRDY
   );

 --  masker_fsm: entity work.fl_masker_fsm
 --  port map(            
 --  CLK           => clk,

  -- synchronous reset
 --   RESET         => reset,
  --input FSM signals
 --   RX_SRC_RDY_N  => RX_SRC_RDY_N,
 --   TX_DST_RDY_N  => TX_DST_RDY_N,
 --   RX_EOF_N      => RX_EOF_N,
 --   RX_SOF_N      => RX_SOF_N,
 --   CONFIG        => reg_config,
  --output FSM signals
 --   FSM_MAY_CONFIG => fsm_may_config,
 --   FSM_RX_DST_RDY_N =>FSM_RX_DST_RDY_N
 -- );   

   -- -------------------------------------------------------------------------
   --                   MI32 Simulation Component
   -- -------------------------------------------------------------------------
   mi32_sim: entity work.mi32_sim
      generic map (
         UPSTREAM_LOG_FILE   => "./mi32.upstream",
         DOWNSTREAM_LOG_FILE => "./mi32.downstream",
         BASE_ADDR           => X"00000000",
         LIMIT               => X"00020000",
         FREQUENCY           => LOCAL_BUS_FREQUENCY,
         BUFFER_EN           => false
      )
      port map (
         -- Common interface
         IB_RESET            => reset,
         IB_CLK              => clk,

         -- User Component Interface
         CLK                 => clk,
         MI32                => mi,

         -- IB SIM interface
         STATUS              => open,
         CTRL                => mi32_sim_ctrl,
         STROBE              => mi32_sim_strobe,
         BUSY                => mi32_sim_busy
     );
   -- -------------------------------------------------------------------------
   --                   FL BFM (FL TX Simulation component)
   -- -------------------------------------------------------------------------
   fl_bfm: entity work.fl_bfm
      generic map (
         DATA_WIDTH     => FL_WIDTH,
         FL_BFM_ID      => 0
      )
      port map (
         -- Common interface
         RESET          => RESET,
         CLK            => CLK,

         -- FrameLink Interface
         TX_DATA        => rx_data,
         TX_REM         => rx_rem,
         TX_SOF_N       => rx_sof_n,
         TX_EOF_N       => rx_eof_n,
         TX_SOP_N       => rx_sop_n,
         TX_EOP_N       => rx_eop_n,
         TX_SRC_RDY_N   => rx_src_rdy_n,
         TX_DST_RDY_N   => rx_dst_rdy_n
      );


   -- -------------------------------------------------------------------------
   --                   FL Simulation Component - RX
   -- -------------------------------------------------------------------------
   fl_monitor: entity work.monitor
      generic map (
         RX_TX_DATA_WIDTH  => FL_WIDTH,
         FILE_NAME         => "./fl_monitor.txt",
         FRAME_PARTS       => FRAME_PARTS,
         RDY_DRIVER        => FLMONITOR_BEHAVIOR
      )
      port map (
         -- Common interface
         FL_RESET          => RESET,
         FL_CLK            => CLK,

         -- RX Frame link Interface
         RX_DATA           => tx_data,
         RX_REM            => tx_rem,
         RX_SOF_N          => tx_sof_n,
         RX_EOF_N          => tx_eof_n,
         RX_SOP_N          => tx_sop_n,
         RX_EOP_N          => tx_eop_n,
         RX_SRC_RDY_N      => tx_src_rdy_n,
         RX_DST_RDY_N      => tx_dst_rdy_n
      );


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
         wait until (clk'event and clk='1' and mi32_sim_busy = '0');
         mi32_sim_ctrl <= ctrl;
         mi32_sim_strobe <= '1';
         wait until (clk'event and clk='1');
         mi32_sim_strobe <= '0';
      end ib_op;

   -- ----------------------------------------------------------------
   --                        Testbench Body
   -- ----------------------------------------------------------------
   begin

--      wait for RESET_DELAY;
--
--      wait for 3*clkper_base;
--      mi.ADDR <= X"00000004";
--      mi.DWR <= X"0F0F0F0F";
--      wait for 3*clkper_base;
--      mi.ADDR <= (others => '0');
--      mi.BE <= (others => '1');
--      mi.DWR <= X"00000002";
--      mi.WR <= '1';
--      wait for 3*clkper_base;
--      mi.ADDR <= X"00000004";
--      mi.DWR <= X"0F0F0F0F";
--      wait for 3*clkper_base;
--      mi.ADDR <= (others => '0');
--      mi.DWR <= (others => '0');
--      wait for 3*clkper_base;
--      mi.WR <= '0';

--      mi.ADDR <= X"00000004";
--      mi.BE <= (others => '1');
--      mi.RD <= '1';
--      wait for 3*clkper_base;
--      mi.RD <= '0';

      wait for RESET_DELAY;
    --MI32 write
      ib_op(ib_local_write(X"00000000", -- dst addr
                           X"11111111", -- src addr
                           1,           -- length of writen data
                           16#ABAB#,    -- Transaction tag
                           '0',         -- trans flag  
                           X"0000000000000002") -- data
                           );
      wait for 100*clkper_base;
      ib_op(ib_local_write(X"00000004", -- dst addr 
                           X"11111111", -- src addr 
                           1,           -- length of bytes to be readed
                           16#ABAB#,    -- transaction tag 
                           '0',
                           X"FFFFFFFFFFFFFF0F")
		          );
      ib_op(ib_local_write(X"00000008", -- dst addr 
                           X"11111111", -- src addr 
                           1,           -- length of bytes to be readed
                           16#ABAB#,    -- transaction tag 
                           '0',
                           X"FFFFFFFFFFFFFF0F")
		          );
      wait for 30*clkper_base;

      ib_op(ib_local_write(X"00000000", -- dst addr
                           X"11111111", -- src addr
                           1,           -- length of writen data
                           16#ABAB#,    -- Transaction tag
                           '0',         -- trans flag  
                           X"0000000000000000") -- data
                           );
      wait;
   end process;

   -- Generate FL input
   flgenp: process
   begin
      wait for RESET_DELAY;

      -- Generate FL input
      SendWriteFile(FLSIM_SEND_FILE, FLBFM_BEHAVIOR, flCmd_0, 0);

      if INFINITE_PCKTS = false then
         wait;
      end if;
   end process;

end architecture testbench_arch;
