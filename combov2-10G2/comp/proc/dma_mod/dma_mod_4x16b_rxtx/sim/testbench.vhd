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
   constant clkper          : time := 5 ns;
   constant reset_time      : time := 10 * clkper;

-- -----------------------Testbench auxilarity signals-------------------------
     -- CLK_GEN Signals
     signal reset : std_logic;
     signal clk   : std_logic;

     -- FrameLink
     signal rx0 : t_fl16;
     signal rx1 : t_fl16;
     signal rx2 : t_fl16;
     signal rx3 : t_fl16;
     signal tx0 : t_fl16;
     signal tx1 : t_fl16;
     signal tx2 : t_fl16;
     signal tx3 : t_fl16;

     -- Internal Bus 64 (IB_SIM)
     signal ib : t_internal_bus64;

     -- IB to IB2LB bridge
     signal ib2lb : t_internal_bus64;
     signal lb : t_local_bus16;
   
     -- IB_SIM component ctrl      
     signal ib_sim_status  : t_ib_status;
     signal ib_sim_ctrl    : t_ib_ctrl;
     signal ib_sim_strobe  : std_logic;
     signal ib_sim_busy    : std_logic;

     signal ib2lb_sim_status  : t_ib_status;
     signal ib2lb_sim_ctrl    : t_ib_ctrl;
     signal ib2lb_sim_strobe  : std_logic;
     signal ib2lb_sim_busy    : std_logic;

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
clk_gen : process
begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
end process;

-- FrameLink generating -------------------------------------------------------
FL_BFM0 : entity work.fl_bfm
   generic map(
      DATA_WIDTH => 16,
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
      DATA_WIDTH => 16,
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

FL_BFM2 : entity work.fl_bfm
   generic map(
      DATA_WIDTH => 16,
      -- uniqe identity of FL_BFM as one of 16 posible FL_BFMs in design
      FL_BFM_ID  => 2
   )
   port map(
      -- Common interface
      RESET        => reset,
      CLK          => clk,

      -- Frame link output Interface 
      TX_DATA      => rx2.data,
      TX_REM       => rx2.drem,
      TX_SOF_N     => rx2.sof_n,
      TX_EOF_N     => rx2.eof_n,
      TX_SOP_N     => rx2.sop_n,
      TX_EOP_N     => rx2.eop_n,
      TX_SRC_RDY_N => rx2.src_rdy_n,
      TX_DST_RDY_N => rx2.dst_rdy_n
     );

FL_BFM3 : entity work.fl_bfm
   generic map(
      DATA_WIDTH => 16,
      -- uniqe identity of FL_BFM as one of 16 posible FL_BFMs in design
      FL_BFM_ID  => 3
   )
   port map(
      -- Common interface
      RESET        => reset,
      CLK          => clk,

      -- Frame link output Interface 
      TX_DATA      => rx3.data,
      TX_REM       => rx3.drem,
      TX_SOF_N     => rx3.sof_n,
      TX_EOF_N     => rx3.eof_n,
      TX_SOP_N     => rx3.sop_n,
      TX_EOP_N     => rx3.eop_n,
      TX_SRC_RDY_N => rx3.src_rdy_n,
      TX_DST_RDY_N => rx3.dst_rdy_n
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

-- Internal Bus simulation ----------------------------------------------------
IB2LB_SIM : entity work.ib_sim
   port map(
      -- Common interface
      IB_RESET     => reset,
      IB_CLK       => clk,

      -- Internal Bus In
      INTERNAL_BUS => ib2lb,

      -- IB SIM interfac
      STATUS       => ib2lb_sim_status,
      CTRL         => ib2lb_sim_ctrl,
      STROBE       => ib2lb_sim_strobe,
      BUSY         => ib2lb_sim_busy
   );

-- DMA module instance --------------------------------------------------------
dma_i : entity work.dma_mod_4x16b_rxtx
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

      RX2_DATA      => rx2.data,
      RX2_DREM      => rx2.drem,
      RX2_SOF_N     => rx2.sof_n,
      RX2_EOF_N     => rx2.eof_n,
      RX2_SOP_N     => rx2.sop_n,
      RX2_EOP_N     => rx2.eop_n,
      RX2_SRC_RDY_N => rx2.src_rdy_n,
      RX2_DST_RDY_N => rx2.dst_rdy_n,

      RX3_DATA      => rx3.data,
      RX3_DREM      => rx3.drem,
      RX3_SOF_N     => rx3.sof_n,
      RX3_EOF_N     => rx3.eof_n,
      RX3_SOP_N     => rx3.sop_n,
      RX3_EOP_N     => rx3.eop_n,
      RX3_SRC_RDY_N => rx3.src_rdy_n,
      RX3_DST_RDY_N => rx3.dst_rdy_n,

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

      TX2_DATA      => tx2.data,
      TX2_DREM      => tx2.drem,
      TX2_SOF_N     => tx2.sof_n,
      TX2_EOF_N     => tx2.eof_n,
      TX2_SOP_N     => tx2.sop_n,
      TX2_EOP_N     => tx2.eop_n,
      TX2_SRC_RDY_N => tx2.src_rdy_n,
      TX2_DST_RDY_N => tx2.dst_rdy_n,

      TX3_DATA      => tx3.data,
      TX3_DREM      => tx3.drem,
      TX3_SOF_N     => tx3.sof_n,
      TX3_EOF_N     => tx3.eof_n,
      TX3_SOP_N     => tx3.sop_n,
      TX3_EOP_N     => tx3.eop_n,
      TX3_SRC_RDY_N => tx3.src_rdy_n,
      TX3_DST_RDY_N => tx3.dst_rdy_n,

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

ib2lb_i : entity work.lb_root
   generic map(
      base_addr      => X"00000000",
      limit          => X"00001000"
   )
   port map(
      IB_CLK         => CLK,
      RESET          => RESET,

      INTERNAL_BUS   => ib2lb,

      LOCAL_BUS      => lb
   );

-- FL - destination is always ready
tx0.dst_rdy_n <= '0';
tx1.dst_rdy_n <= '0';
tx2.dst_rdy_n <= '0';
tx3.dst_rdy_n <= '0';

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

-- Support for ib2lb_op
procedure ib2lb_op(ctrl : in t_ib_ctrl) is
begin
   wait until (CLK'event and CLK='1' and ib2lb_sim_busy = '0');
   ib2lb_sim_ctrl   <= ctrl;
   ib2lb_sim_strobe <= '1';
   wait until (CLK'event and CLK='1');
   ib2lb_sim_strobe <= '0';
end ib2lb_op;

-- start testing ---------------------------------------------------------------
begin
   

   wait for reset_time;
   wait until (CLK'event and CLK='1');

   wait for 10*clkper;

   -- WWW
   ib2lb_op(ib_local_write(X"0000084C", X"F0000000", 
                           4, 16#ABAB#, '0', 
                           X"00000000AAAAAAA0"));
   ib2lb_op(ib_local_write(X"000008CC", X"F0000000", 
                           4, 16#ABAB#, '0', 
                           X"00000000AAAAAAA1"));
   ib2lb_op(ib_local_write(X"0000094C", X"F0000000", 
                           4, 16#ABAB#, '0', 
                           X"00000000AAAAAAA2"));


   -- WWW
   ib2lb_op(ib_local_write(X"0000084C", X"F0000000", 
                           4, 16#ABAB#, '0', 
                           X"00000000BBBBBBB0"));
   ib2lb_op(ib_local_write(X"000008CC", X"F0000000", 
                           4, 16#ABAB#, '0', 
                           X"00000000BBBBBBB1"));
   ib2lb_op(ib_local_write(X"0000094C", X"F0000000", 
                           4, 16#ABAB#, '0', 
                           X"00000000BBBBBBB2"));


   -- WWW
   ib2lb_op(ib_local_write(X"0000084C", X"F0000000", 
                           4, 16#ABAB#, '0', 
                           X"00000000DDDDDDD0"));
   ib2lb_op(ib_local_write(X"000008CC", X"F0000000", 
                           4, 16#ABAB#, '0', 
                           X"00000000DDDDDDD1"));
   ib2lb_op(ib_local_write(X"0000094C", X"F0000000", 
                           4, 16#ABAB#, '0', 
                           X"00000000DDDDDDD2"));


   -- RRR
   ib2lb_op(ib_local_read(X"0000084C", X"F0000000",
                          4, 16#ABAB#, false));
   ib2lb_op(ib_local_read(X"000008CC", X"F0000000",
                          4, 16#ABAB#, false));
   ib2lb_op(ib_local_read(X"0000094C", X"F0000000",
                          4, 16#ABAB#, false));


   -- RWRWR
   ib2lb_op(ib_local_read(X"0000084C", X"F0000000",
                          4, 16#ABAB#, false));
   ib2lb_op(ib_local_write(X"0000084C", X"F0000000", 
                           4, 16#ABAB#, '0', 
                           X"00000000CCCCCCC0"));
   ib2lb_op(ib_local_read(X"0000084C", X"F0000000",
                          4, 16#ABAB#, false));
   ib2lb_op(ib_local_write(X"0000084C", X"F0000000", 
                           4, 16#ABAB#, '0', 
                           X"00000000EEEEEEE0"));
   ib2lb_op(ib_local_read(X"0000084C", X"F0000000",
                          4, 16#ABAB#, false));

   -- RWRWR
   ib2lb_op(ib_local_read(X"000008CC", X"F0000000",
                          4, 16#ABAB#, false));
   ib2lb_op(ib_local_write(X"000008CC", X"F0000000", 
                           4, 16#ABAB#, '0', 
                           X"00000000CCCCCCC1"));
   ib2lb_op(ib_local_read(X"000008CC", X"F0000000",
                          4, 16#ABAB#, false));
   ib2lb_op(ib_local_write(X"000008CC", X"F0000000", 
                           4, 16#ABAB#, '0', 
                           X"00000000EEEEEEE1"));
   ib2lb_op(ib_local_read(X"000008CC", X"F0000000",
                          4, 16#ABAB#, false));

   -- RWRWR
   ib2lb_op(ib_local_read(X"0000094C", X"F0000000",
                          4, 16#ABAB#, false));
   ib2lb_op(ib_local_write(X"0000094C", X"F0000000", 
                           4, 16#ABAB#, '0', 
                           X"00000000CCCCCCC2"));
   ib2lb_op(ib_local_read(X"0000094C", X"F0000000",
                          4, 16#ABAB#, false));
   ib2lb_op(ib_local_write(X"0000094C", X"F0000000", 
                           4, 16#ABAB#, '0', 
                           X"00000000EEEEEEE2"));
   ib2lb_op(ib_local_read(X"0000094C", X"F0000000",
                          4, 16#ABAB#, false));

   wait;
end process;


end architecture TESTBENCH_arch;
