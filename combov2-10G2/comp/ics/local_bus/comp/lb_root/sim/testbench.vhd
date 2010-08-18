--
-- TESTBENCH.vhd: testbench
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
use work.ib_pkg.all; -- Internal Bus Package
use work.lb_pkg.all; -- Local Bus Package
use work.ib_sim_oper.all; -- Internal Bus Simulation Package

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity TESTBENCH is
end entity TESTBENCH;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture TESTBENCH_ARCH of TESTBENCH is


-- -----------------------Testbench constant-----------------------------------
   constant UUT_BASE_ADDR   : std_logic_vector(31 downto 0) := X"11111100";
   constant UUT_LIMIT       : std_logic_vector(31 downto 0) := X"00000100"; -- 256 Bytes

   constant clkper_50       : time    := 20 ns;
   constant clkper_100      : time    := 10 ns;
   constant reset_time      : time    := 100 * clkper_100;

-- -----------------------Testbench auxilarity signals-------------------------
   -- CLK_GEN Signals
   signal reset               : std_logic;
   signal clk                 : std_logic;
   signal clk_50_in           : std_logic;
   signal clk50               : std_logic;
   signal clk100              : std_logic;
   signal ib_clk              : std_logic;
   signal lb_clk              : std_logic;
   signal lock                : std_logic;

   -- Internal Bus 64 (IB_SIM)
   signal internal_bus64      : t_internal_bus64;

   -- IB Switch1 Map
   signal switch1_port1       : t_internal_bus64;
   signal switch1_port2       : t_internal_bus64;

   -- Local Bus 16 (LB_ROOT)
   signal local_bus16         : t_local_bus16;

   -- LB Switch1 Map
   signal lb_switch1_port1    : t_local_bus16;
   signal lb_switch1_port2    : t_local_bus16;

   -- LB Endpoint
   signal lb_mi32             : t_mi32;
 
   -- IB_SIM component ctrl      
   signal ib_sim_ctrl         : t_ib_ctrl;
   signal ib_sim_strobe       : std_logic;
   signal ib_sim_busy         : std_logic;
     
begin

-- Reset generation -----------------------------------------------------------
RESET_GEN : process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process reset_gen;
   
-- clk50 generator ------------------------------------------------------------
CLK50_GEN : process
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

clk    <= clk100;
ib_clk <= clk100;
lb_clk <= clk100;
   
-- Internal Bus Switch --------------------------------------------------------
switch1 : entity work.IB_SWITCH
   generic map (
      -- Data Width (64/128)
      DATA_WIDTH        => 64,
      -- Port 0 Address Space
      SWITCH_BASE        => UUT_BASE_ADDR,
      SWITCH_LIMIT       => X"30000000",
      -- Port 1 Address Space
      DOWNSTREAM0_BASE   => UUT_BASE_ADDR,
      DOWNSTREAM0_LIMIT  => X"10000000",
      -- Port 2 Address Space
      DOWNSTREAM1_BASE   => X"22222220", 
      DOWNSTREAM1_LIMIT  => X"00000100"
   )

   port map (
      -- Common Interface
      IB_CLK         => ib_clk,
      IB_RESET       => reset,
      -- Upstream Port
      PORT0          => internal_bus64,
      -- Downstream Ports
      PORT1          => switch1_port1,
      PORT2          => switch1_port2
   );

-- -----------------------Portmaping of LB root -------------------------------
LB_ROOT_U : entity work.LB_ROOT
   generic map (
      BASE_ADDR      => UUT_BASE_ADDR,
      LIMIT          => X"00010000" -- ADDR_WIDTH=16
   )
   port map (
      -- Common Interface
      IB_CLK         => ib_clk,
      RESET          => reset,

      -- Local Bus Interface
      INTERNAL_BUS   => switch1_port1,

      -- Local Bus Interface
      LOCAL_BUS      => local_bus16
  );

-- -----------------------Portmaping of LB switch -----------------------------
LB_SWITCH3_U : entity work.LB_SWITCH_NOREC
   generic map(
      PORT_COUNT  => 2
   )
   port map(
      LB_CLK        => lb_clk,
      LB_RESET      => reset,

      -- Upstream port
      PORT0_DWR     => local_bus16.dwr,
      PORT0_BE      => local_bus16.be,
      PORT0_ADS_N   => local_bus16.ads_n,
      PORT0_RD_N    => local_bus16.rd_n,
      PORT0_WR_N    => local_bus16.wr_n,
      PORT0_DRD     => local_bus16.drd,
      PORT0_RDY_N   => local_bus16.rdy_n,
      PORT0_ERR_N   => local_bus16.err_n,
      PORT0_ABORT_N => local_bus16.abort_n,

      -- Downstream ports
      DWR(15 downto 0)  => lb_switch1_port1.dwr,
      DWR(31 downto 16) => lb_switch1_port2.dwr,
      BE(1 downto 0)    => lb_switch1_port1.be,
      BE(3 downto 2)    => lb_switch1_port2.be,
      ADS_N(0)          => lb_switch1_port1.ads_n,
      ADS_N(1)          => lb_switch1_port2.ads_n,
      RD_N(0)           => lb_switch1_port1.rd_n,
      RD_N(1)           => lb_switch1_port2.rd_n,
      WR_N(0)           => lb_switch1_port1.wr_n,
      WR_N(1)           => lb_switch1_port2.wr_n,
      DRD(15 downto 0)  => lb_switch1_port1.drd,
      DRD(31 downto 16) => lb_switch1_port2.drd,
      RDY_N(0)          => lb_switch1_port1.rdy_n,
      RDY_N(1)          => lb_switch1_port2.rdy_n,
      ERR_N(0)          => lb_switch1_port1.err_n,
      ERR_N(1)          => lb_switch1_port2.err_n,
      ABORT_N(0)        => lb_switch1_port1.abort_n,
      ABORT_N(1)        => lb_switch1_port2.abort_n
   );

-- -----------------------Portmaping of LB_Endpoint ---------------------------   
LB_ENDPOINT_U : entity work.LB_ENDPOINT
   generic map (
      BASE_ADDR      => UUT_BASE_ADDR,
      LIMIT          => UUT_LIMIT, -- ADDR_WIDTH=8
      FREQUENCY      => LOCAL_BUS_FREQUENCY,
      BUFFER_EN      => false
   )
   port map (
      -- Common Interface
      RESET          => reset,

      -- Local Bus Interface
      LB_CLK         => lb_clk,
      LOCALBUS       => lb_switch1_port1,

      -- User Component Interface
      CLK            => CLK,
      MI32           => lb_mi32
  );

-- ---------------- Memory connected to LB_Endpoint ---------------------------
MI32MEM_U : entity work.MI32MEM
   generic map (
      SIZE         => 256, -- Size of memory in bytes
      BRAM_DISTMEM => 0    -- 0 = BRAM / 1 = DISTMEM
    )
   port map (
      -- Common Interface
      CLK          => CLK,
      RESET        => RESET,
      -- MI32 Interface
      MI32         => lb_mi32
   );

-- Internal Bus simulation component ------------------------------------------
IB_SIM_U : entity work.IB_SIM
   generic map (
      UPSTREAM_LOG_FILE   => "ib_upstream_log.txt",
      DOWNSTREAM_LOG_FILE => "ib_downstream_log.txt"
   )
   port map (
      -- Common interface
      IB_RESET           => reset,
      IB_CLK             => ib_clk,

      -- Internal Bus Interface
      INTERNAL_BUS       => internal_bus64,

      -- IB SIM interface
      CTRL               => ib_sim_ctrl,
      STROBE             => ib_sim_strobe,
      BUSY               => ib_sim_busy
      );

tb : process
-- ----------------------------------------------------------------------------
--                                 Procedures declaration
-- ----------------------------------------------------------------------------

-- ----------------------------------------------------------------------------
-- Support for ib_op
procedure ib_op(ctrl : in t_ib_ctrl) is
begin
   wait until (IB_CLK'event and IB_CLK='1' and ib_sim_busy = '0');
   ib_sim_ctrl <= ctrl;
   ib_sim_strobe <= '1';
   wait until (IB_CLK'event and IB_CLK='1');
   ib_sim_strobe <= '0';
end ib_op;

-- start testing ---------------------------------------------------------------
begin

   -- IB_SWITCH_PORT2 UNUSED
   switch1_port2.UP.src_rdy_n    <= '1';  -- Data Is Not Ready
   switch1_port2.UP.eop_n        <= '1';  -- Not EOP
   switch1_port2.UP.sop_n        <= '1';  -- Not SOP
   switch1_port2.UP.data         <= X"0000000000000000"; -- DATA
   switch1_port2.DOWN.dst_rdy_n  <= '0'; -- Dst Rdy

   -- LB_SWITCH_PORT1 UNUSED
   lb_switch1_port2.ERR_N <= '1';
   lb_switch1_port2.RDY_N <= '1';
   lb_switch1_port2.DRD   <= (others => '0');

   -- TESTBENCH
   wait for reset_time;

   -- Write first 64 words and read it
   ib_op(ib_local_write(UUT_BASE_ADDR, X"00000000", 4, 16#ABAB#, '0', X"ABABABABABABABAB"));
   ib_op(ib_local_write(UUT_BASE_ADDR+4, X"00000000", 4, 16#ABAB#, '0', X"CDCDCDCDCDCDCDCD"));
   ib_op(ib_local_read(UUT_BASE_ADDR, X"00000002", 8, 16#ABAB#));
   ib_op(ib_local_write(UUT_BASE_ADDR+2, X"00000000", 4, 16#ABAB#, '0', X"EFEFEFEFEFEFEFEF"));
   ib_op(ib_local_read(UUT_BASE_ADDR, X"00000002", 8, 16#ABAB#));

   -- Fill whole memory
   ib_op(ib_local_write_file(UUT_BASE_ADDR, X"00000000", 256, 16#ABAB#, '0', "./tests/test_write0.txt"));
   ib_op(ib_local_read(UUT_BASE_ADDR, X"00000002", 256, 16#ABAB#));
   wait;
end process;

end architecture TESTBENCH_ARCH; 
