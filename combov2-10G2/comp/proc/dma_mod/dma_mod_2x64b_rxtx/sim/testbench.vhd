-- testbench.vhd: dma module testbench
-- Copyright (C) 2009 CESNET
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
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;
use work.fl_pkg.all; -- FrameLink Package
use work.ib_pkg.all; -- Internal Bus Package
use work.lb_pkg.all; -- Local Bus Package
use work.ib_sim_oper.all; -- Internal Bus Simulation Package
use work.fl_bfm_rdy_pkg.all; -- FrameLink BFM packages
use work.fl_bfm_pkg.all; 

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity TESTBENCH is
end entity TESTBENCH;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture TESTBENCH_arch of TESTBENCH is

-- -----------------------Testbench constant-----------------------------------
   constant clkper          : time := 8 ns;
   constant reset_time      : time := 10 * clkper;

-- -----------------------Testbench auxilarity signals-------------------------
     -- CLK_GEN Signals
     signal reset : std_logic;
     signal clk   : std_logic;

     -- FrameLink
     signal rx0 : t_fl64;
     signal rx1 : t_fl64;
     signal tx0 : t_fl64;
     signal tx1 : t_fl64;

     -- Internal Bus 64 (IB_SIM)
     signal ib : t_internal_bus64;
     signal lb : t_local_bus16;
   
     -- IB_SIM component ctrl      
     signal ib_sim_status  : t_ib_status;
     signal ib_sim_ctrl    : t_ib_ctrl;
     signal ib_sim_strobe  : std_logic;
     signal ib_sim_busy    : std_logic;

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
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
end process;

-- FrameLink generating -------------------------------------------------------
FL_BFM0 : entity work.fl_bfm
   generic map(
      DATA_WIDTH => 64,
      -- uniqe identity of FL_BFM as one of 16 posible FL_BFMs in design
      FL_BFM_ID  => 0
   )
   port map(
      -- Common interface
      RESET        => reset,
      CLK          => clk,

      -- Frame link output Interface 
      TX_DATA      => rx0.data,
      TX_REM       => rx0.drem,
      TX_SOF_N     => rx0.sof_n,
      TX_EOF_N     => rx0.eof_n,
      TX_SOP_N     => rx0.sop_n,
      TX_EOP_N     => rx0.eop_n,
      TX_SRC_RDY_N => rx0.src_rdy_n,
      TX_DST_RDY_N => rx0.dst_rdy_n
     );

FL_BFM1 : entity work.fl_bfm
   generic map(
      DATA_WIDTH => 64,
      -- uniqe identity of FL_BFM as one of 16 posible FL_BFMs in design
      FL_BFM_ID  => 1
   )
   port map(
      -- Common interface
      RESET        => reset,
      CLK          => clk,

      -- Frame link output Interface 
      TX_DATA      => rx1.data,
      TX_REM       => rx1.drem,
      TX_SOF_N     => rx1.sof_n,
      TX_EOF_N     => rx1.eof_n,
      TX_SOP_N     => rx1.sop_n,
      TX_EOP_N     => rx1.eop_n,
      TX_SRC_RDY_N => rx1.src_rdy_n,
      TX_DST_RDY_N => rx1.dst_rdy_n
     );

-- Internal Bus simulation ----------------------------------------------------
IB_SIM : entity work.ib_sim
   port map(
      -- Common interface
      IB_RESET     => reset,
      IB_CLK       => clk,

      -- Internal Bus In
      INTERNAL_BUS => ib,

      -- IB SIM interfac
      STATUS       => ib_sim_status,
      CTRL         => ib_sim_ctrl,
      STROBE       => ib_sim_strobe,
      BUSY         => ib_sim_busy
   );

-- DMA module instance --------------------------------------------------------
dma_i : entity work.dma_mod_2x64b_rxtx
   port map(
      -- ICS Clock and RESET - drives almost whole module, also IB and LB ifcs
      CLK           => clk,
      RESET         => reset,

      -- USER Clock and RESET - driver FL_ASFIFOs and FL ifcs
      USER_CLK      => clk,
      USER_RESET    => reset,

      -- Synchronous at CLK (ICS Clock)
      RX_INTERRUPT  => open,
      TX_INTERRUPT  => open,
      
      -- network interfaces - USER_CLK
      -- input interface
      RX0_DATA      => rx0.data,
      RX0_DREM      => rx0.drem,
      RX0_SOF_N     => rx0.sof_n,
      RX0_EOF_N     => rx0.eof_n,
      RX0_SOP_N     => rx0.sop_n,
      RX0_EOP_N     => rx0.eop_n,
      RX0_SRC_RDY_N => rx0.src_rdy_n,
      RX0_DST_RDY_N => rx0.dst_rdy_n,

      RX1_DATA      => rx1.data,
      RX1_DREM      => rx1.drem,
      RX1_SOF_N     => rx1.sof_n,
      RX1_EOF_N     => rx1.eof_n,
      RX1_SOP_N     => rx1.sop_n,
      RX1_EOP_N     => rx1.eop_n,
      RX1_SRC_RDY_N => rx1.src_rdy_n,
      RX1_DST_RDY_N => rx1.dst_rdy_n,

       -- output interfaces
      TX0_DATA      => tx0.data,
      TX0_DREM      => tx0.drem,
      TX0_SOF_N     => tx0.sof_n,
      TX0_EOF_N     => tx0.eof_n,
      TX0_SOP_N     => tx0.sop_n,
      TX0_EOP_N     => tx0.eop_n,
      TX0_SRC_RDY_N => tx0.src_rdy_n,
      TX0_DST_RDY_N => tx0.dst_rdy_n,

      TX1_DATA      => tx1.data,
      TX1_DREM      => tx1.drem,
      TX1_SOF_N     => tx1.sof_n,
      TX1_EOF_N     => tx1.eof_n,
      TX1_SOP_N     => tx1.sop_n,
      TX1_EOP_N     => tx1.eop_n,
      TX1_SRC_RDY_N => tx1.src_rdy_n,
      TX1_DST_RDY_N => tx1.dst_rdy_n,

      -- Internal Bus - CLK (ICS Clock)
      IB_DOWN_DATA      => ib.down.data,
      IB_DOWN_SOP_N     => ib.down.sop_n,
      IB_DOWN_EOP_N     => ib.down.eop_n,
      IB_DOWN_SRC_RDY_N => ib.down.src_rdy_n,
      IB_DOWN_DST_RDY_N => ib.down.dst_rdy_n,
      IB_UP_DATA        => ib.up.data,
      IB_UP_SOP_N       => ib.up.sop_n,
      IB_UP_EOP_N       => ib.up.eop_n,
      IB_UP_SRC_RDY_N   => ib.up.src_rdy_n,
      IB_UP_DST_RDY_N   => ib.up.dst_rdy_n,

      -- Local Bus - CLK (ICS Clock)
      LB_DWR     => lb.dwr,
      LB_BE      => lb.be,
      LB_ADS_N   => lb.ads_n,
      LB_RD_N    => lb.rd_n,
      LB_WR_N    => lb.wr_n,
      LB_DRD     => lb.drd,
      LB_RDY_N   => lb.rdy_n,
      LB_ERR_N   => lb.err_n,
      LB_ABORT_N => lb.abort_n
   );

-- FL - destination is always ready
tx0.dst_rdy_n <= '0';
tx1.dst_rdy_n <= '0';

tb : process
-- ----------------------------------------------------------------------------
--                                 Procedures declaration
-- ----------------------------------------------------------------------------
-- ----------------------------------------------------------------------------
-- Support for ib_op
procedure ib_op(ctrl : in t_ib_ctrl) is
begin
   wait until (CLK'event and CLK='1' and ib_sim_busy = '0');
   ib_sim_ctrl   <= ctrl;
   ib_sim_strobe <= '1';
   wait until (CLK'event and CLK='1');
   ib_sim_strobe <= '0';
end ib_op;

-- start testing ---------------------------------------------------------------
begin
   
   lb.dwr <= X"0000";
   lb.be <= "11";
   lb.ads_n <= '1';
   lb.rd_n <= '1';
   lb.wr_n <= '1';
   lb.abort_n <= '1';

   wait for reset_time;
   wait until (CLK'event and CLK='1');

   wait for 10*clkper;

   -- TX Channel 0 init -------------------------------------------------------
   -- 03FF FFFF -> 850
   lb.ads_n <= '0';
   lb.dwr <= X"0850";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.ads_n <= '1';
   lb.wr_n <= '0';
   lb.dwr <= X"FFFF";
   wait for clkper;
   lb.dwr <= X"03FF";
   wait for clkper;
   lb.wr_n <= '1';

   wait for 5*clkper;

   ib_op(ib_local_write(X"02240008", X"F0000000",  4, 16#ABAB#, '0', X"00000000091FF001"));
   ib_op(ib_local_write(X"0224000C", X"F0000000",  4, 16#ABAB#, '0', X"000024DA00000000"));

   wait for 5*clkper;

   -- 0 -> 848
   lb.ads_n <= '0';
   lb.dwr <= X"0848";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.ads_n <= '1';
   lb.wr_n <= '0';
   lb.dwr <= X"0000";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.wr_n <= '1';

   wait for 5*clkper;

   -- 0 -> 84C
   lb.ads_n <= '0';
   lb.dwr <= X"084C";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.ads_n <= '1';
   lb.wr_n <= '0';
   lb.dwr <= X"0000";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.wr_n <= '1';

   wait for 5*clkper;

   -- 1 -> 840
   lb.ads_n <= '0';
   lb.dwr <= X"0840";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.ads_n <= '1';
   lb.wr_n <= '0';
   lb.dwr <= X"0001";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.wr_n <= '1';

   wait for 5*clkper;

   -- (2) <- 844
   lb.ads_n <= '0';
   lb.dwr <= X"0844";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.ads_n <= '1';
   lb.rd_n <= '0';
   wait for clkper;
   wait for clkper;
   lb.rd_n <= '1';

   wait for 15*clkper;

   ib_op(ib_read_completition(X"02201000", X"F0000000", 32, 255, "data/desc1.txt"));

   wait for 30*clkper;

   ib_op(ib_read_completition(X"02201020", X"F0000000", 32, 255, "data/desc2.txt"));

   -- TX Channel 1 init -----------------------------------------------------
   wait for 30*clkper;
   -- 03FF FFFF -> 8D0
   lb.ads_n <= '0';
   lb.dwr <= X"08D0";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.ads_n <= '1';
   lb.wr_n <= '0';
   lb.dwr <= X"FFFF";
   wait for clkper;
   lb.dwr <= X"03FF";
   wait for clkper;
   lb.wr_n <= '1';

   wait for 5*clkper;

   ib_op(ib_local_write(X"02240018", X"F0000000",  4, 16#ABAB#, '0', X"0000000002A2F001"));
   ib_op(ib_local_write(X"0224001C", X"F0000000",  4, 16#ABAB#, '0', X"1C0024DA00000000"));

   wait for 5*clkper;

   -- 0 -> 8C8
   lb.ads_n <= '0';
   lb.dwr <= X"08C8";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.ads_n <= '1';
   lb.wr_n <= '0';
   lb.dwr <= X"0000";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.wr_n <= '1';

   wait for 5*clkper;

   -- 0 -> 8CC
   lb.ads_n <= '0';
   lb.dwr <= X"08CC";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.ads_n <= '1';
   lb.wr_n <= '0';
   lb.dwr <= X"0000";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.wr_n <= '1';

   wait for 5*clkper;

   -- 1 -> 8C0
   lb.ads_n <= '0';
   lb.dwr <= X"08C0";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.ads_n <= '1';
   lb.wr_n <= '0';
   lb.dwr <= X"0001";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.wr_n <= '1';

   wait for 5*clkper;

   -- (2) <- 8C4
   lb.ads_n <= '0';
   lb.dwr <= X"08C4";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.ads_n <= '1';
   lb.rd_n <= '0';
   wait for clkper;
   wait for clkper;
   lb.rd_n <= '1';

   wait for 15*clkper;

   ib_op(ib_read_completition(X"02203000", X"F0000000", 32, 255, "data/desc3.txt"));

   wait for 30*clkper;

   ib_op(ib_read_completition(X"02203020", X"F0000000", 32, 255, "data/desc4.txt"));

   wait for 30*clkper;

   -- TX Channel 0 start -----------------------------------------------------

   -- (0) <- 84C
   lb.ads_n <= '0';
   lb.dwr <= X"084C";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.ads_n <= '1';
   lb.rd_n <= '0';
   wait for clkper;
   wait for clkper;
   lb.rd_n <= '1';

   wait for 5*clkper;

   -- (0) <- 848
   lb.ads_n <= '0';
   lb.dwr <= X"0848";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.ads_n <= '1';
   lb.rd_n <= '0';
   wait for clkper;
   wait for clkper;
   lb.rd_n <= '1';

   wait for 5*clkper;

   -- (0) <- 84C
   lb.ads_n <= '0';
   lb.dwr <= X"084C";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.ads_n <= '1';
   lb.rd_n <= '0';
   wait for clkper;
   wait for clkper;
   lb.rd_n <= '1';

   wait for 5*clkper;

   -- 5F8 -> 84C
   lb.ads_n <= '0';
   lb.dwr <= X"084C";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.ads_n <= '1';
   lb.wr_n <= '0';
   lb.dwr <= X"05F8";
   wait for clkper;
   lb.dwr <= X"0000";
   wait for clkper;
   lb.wr_n <= '1';

   wait for 5*clkper;
   ib_op(ib_read_completition_nolast(X"02100000", X"F0000000", 64, 5, "data/pac1.txt"));
   wait for 5*clkper;
   ib_op(ib_read_completition_nolast(X"02100040", X"F0000000", 64, 5, "data/pac1.txt"));
   wait for 5*clkper;
   ib_op(ib_read_completition_nolast(X"02100080", X"F0000000", 128, 5, "data/pac1.txt"));

   wait for 5*clkper;
   ib_op(ib_read_completition_nolast(X"02100100", X"F0000000", 64, 5, "data/pac1.txt"));
   wait for 5*clkper;
   ib_op(ib_read_completition_nolast(X"02100140", X"F0000000", 64, 5, "data/pac1.txt"));
   wait for 5*clkper;
   ib_op(ib_read_completition_nolast(X"02100180", X"F0000000", 128, 5, "data/pac1.txt"));

   wait for 5*clkper;
   ib_op(ib_read_completition_nolast(X"02100200", X"F0000000", 128, 5, "data/pac1.txt"));
   wait for 5*clkper;
   ib_op(ib_read_completition_nolast(X"02100280", X"F0000000", 128, 5, "data/pac1.txt"));
   wait for 5*clkper;
   ib_op(ib_read_completition_nolast(X"02100300", X"F0000000", 64, 5, "data/pac1.txt"));

   wait for 5*clkper;
   ib_op(ib_read_completition_nolast(X"02100340", X"F0000000", 64, 5, "data/pac1.txt"));
   wait for 5*clkper;
   ib_op(ib_read_completition_nolast(X"02100380", X"F0000000", 128, 5, "data/pac1.txt"));
   wait for 5*clkper;
   ib_op(ib_read_completition_nolast(X"02100400", X"F0000000", 128, 5, "data/pac1.txt"));

   wait for 5*clkper;
   ib_op(ib_read_completition_nolast(X"02100480", X"F0000000", 128, 5, "data/pac1.txt"));
   wait for 5*clkper;
   ib_op(ib_read_completition_nolast(X"02100500", X"F0000000", 64, 5, "data/pac1.txt"));
   wait for 5*clkper;
   ib_op(ib_read_completition_nolast(X"02100540", X"F0000000", 64, 5, "data/pac1.txt"));

   wait for 5*clkper;
   ib_op(ib_read_completition_nolast(X"02100580", X"F0000000", 64, 5, "data/pac1.txt"));
   wait for 5*clkper;
   ib_op(ib_read_completition(X"021005C0", X"F0000000", 56, 5, "data/pac1.txt"));


   wait for 30*clkper;
   
   -- generate soome FrameLink traffic
   SendWriteFile ("data/fl_rx_data.txt", EVER, flCmd_0, 0);

   wait;
end process;


end architecture TESTBENCH_arch;
