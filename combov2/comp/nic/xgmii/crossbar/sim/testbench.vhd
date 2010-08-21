-- TESTBENCH.vhd: testbench
-- Copyright (C) 2006 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
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
architecture TESTBENCH_arch of TESTBENCH is

   constant clkper_50       : time    := 20 ns;
   constant clkper_100      : time    := 10 ns;
   constant reset_time      : time    := 100 * clkper_100;
   constant UUT_BASE_ADDR   : std_logic_vector(31 downto 0) := X"11111100";
   constant UUT_LIMIT       : std_logic_vector(31 downto 0) := X"00000100";
     
   signal reset               : std_logic;
   signal clk                 : std_logic;
   signal clk_50_in           : std_logic;
   signal clk50               : std_logic;
   signal clk100              : std_logic;
   signal ib_clk              : std_logic;
   signal lb_clk              : std_logic;
   signal lock                : std_logic;
     
   signal lb_mi32             : t_mi32;

   -- IB_SIM component ctrl      
   signal ib_sim_ctrl         : t_ib_ctrl;
   signal ib_sim_strobe       : std_logic;
   signal ib_sim_busy         : std_logic;
   signal drd_cnt             : std_logic_vector(31 downto 0);
   signal drdy_rd_pipe        : std_logic_vector(9 downto 0);
   signal ardy_pipe           : std_logic_vector(9 downto 0);
   signal drd_cnt_ce          : std_logic;

   signal crossbar_sop        : std_logic_vector(5 downto 0);
   signal crossbar_eop        : std_logic_vector(5 downto 0);

begin

   -- Reset generation
   reset_gen : process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process reset_gen;
   
   -- clk50 generator
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

   clk    <= clk100;
   ib_clk <= clk100;
   lb_clk <= clk100;

   CROSSBAR_TOP_U : entity work.XGMII_CROSSBAR_TOP
   generic map (
      XGMII_COUNT => 6
   )
   port map (
      CLK   => clk,
      RESET => reset,

      XGMII_RXC   => (others => 'X'),
      XGMII_RXD   => (others => 'X'),
      XGMII_TXC   => open,
      XGMII_TXD   => open,

      RX_SOP      => crossbar_sop,
      RX_EOP      => crossbar_eop,
      TX_SOP      => open,
      TX_EOP      => open,

      DWR      => lb_mi32.dwr,
      ADDR     => lb_mi32.addr,
      RD       => lb_mi32.rd,
      WR       => lb_mi32.wr,
      BE       => lb_mi32.be,
      DRD      => lb_mi32.drd,
      ARDY     => lb_mi32.ardy,
      DRDY     => lb_mi32.drdy
   );

--   CROSSBAR_CONFIG_U : entity work.XGMII_CROSSBAR_CONFIG
--   generic map (
--      XGMII_COUNT => 6
--   )
--   port map (
--      CLK   => clk,
--      RESET => reset,
--
--      MAPPING  => open,
--
--      DWR      => lb_mi32.dwr,
--      ADDR     => lb_mi32.addr,
--      RD       => lb_mi32.rd,
--      WR       => lb_mi32.wr,
--      BE       => lb_mi32.be,
--      DRD      => lb_mi32.drd,
--      ARDY     => lb_mi32.ardy,
--      DRDY     => lb_mi32.drdy
--   );
 
   -- Internal Bus simulation component
   MI32_SIM_U : entity work.MI32_SIM
   generic map (
      UPSTREAM_LOG_FILE   => "ib_upstream_log.txt",
      DOWNSTREAM_LOG_FILE => "ib_downstream_log.txt",
      BASE_ADDR           => UUT_BASE_ADDR,
      LIMIT               => UUT_LIMIT,
      FREQUENCY           => LOCAL_BUS_FREQUENCY,
      BUFFER_EN           => false
   )
   port map (
      -- Common interface
      IB_RESET           => reset,
      IB_CLK             => ib_clk,

      -- User Component Interface
      CLK                => clk,
      MI32               => lb_mi32,

      -- IB SIM interface
      CTRL               => ib_sim_ctrl,
      STROBE             => ib_sim_strobe,
      BUSY               => ib_sim_busy
   );

tb : process
   
   procedure ib_op(ctrl : in t_ib_ctrl) is
   begin
      wait until (IB_CLK'event and IB_CLK='1' and ib_sim_busy = '0');
      ib_sim_ctrl <= ctrl;
      ib_sim_strobe <= '1';
      wait until (IB_CLK'event and IB_CLK='1');
      ib_sim_strobe <= '0';
   end ib_op;

begin
   -- Testbench
   wait for reset_time;

   -- * < A
   ib_op(ib_local_write(X"11111100", X"00000000", 4, 16#ABAB#, '0', X"0000000000000000"));
   for i in 1 to 32 loop
      wait until clk'event and clk = '1';
   end loop;

   -- * < A
   -- A < E
   ib_op(ib_local_write(X"11111100", X"00000000", 4, 16#ABAB#, '0', X"0000000000000004"));
   for i in 1 to 32 loop
      wait until clk'event and clk = '1';
   end loop;
   
   -- A < A
   -- B < B
   -- C < C
   -- D < D
   -- E < E
   -- F < F
   ib_op(ib_local_write(X"11111100", X"00000000", 4, 16#ABAB#, '0', X"000000000002C688"));
   for i in 1 to 32 loop
      wait until clk'event and clk = '1';
   end loop;

   -- A < E
   -- B < B
   -- C < C
   -- D < D
   -- E < A
   -- F < A
   ib_op(ib_local_write(X"11111100", X"00000000", 4, 16#ABAB#, '0', X"000000000000068C"));
   for i in 1 to 32 loop
      wait until clk'event and clk = '1';
   end loop;
end process;

packet0: process
begin
   crossbar_sop(0) <= '0';
   crossbar_eop(0) <= '0';

   if reset = '1' then
      wait until reset = '0';
   end if;

   wait until clk'event and clk = '1';
   crossbar_sop(0) <= '1';
   crossbar_eop(0) <= '0';

   wait until clk'event and clk = '1';
   crossbar_sop(0) <= '0';
   crossbar_eop(0) <= '0';

   wait until clk'event and clk = '1';
   wait until clk'event and clk = '1';
   crossbar_sop(0) <= '0';
   crossbar_eop(0) <= '1';
   
   wait until clk'event and clk = '1';
end process;

packet1: process
begin
   crossbar_sop(1) <= '0';
   crossbar_eop(1) <= '0';

   if reset = '1' then
      wait until reset = '0';
   end if;

   wait until clk'event and clk = '1';
   wait until clk'event and clk = '1';
   wait until clk'event and clk = '1';
   crossbar_sop(1) <= '1';
   crossbar_eop(1) <= '0';

   wait until clk'event and clk = '1';
   crossbar_sop(1) <= '0';
   crossbar_eop(1) <= '0';

   wait until clk'event and clk = '1';
   crossbar_sop(1) <= '0';
   crossbar_eop(1) <= '1';

   wait until clk'event and clk = '1';
   crossbar_sop(1) <= '0';
   crossbar_eop(1) <= '0';
   
   wait until clk'event and clk = '1';
end process;

packet2: process
begin
   crossbar_sop(2) <= '0';
   crossbar_eop(2) <= '0';

   if reset = '1' then
      wait until reset = '0';
   end if;

   crossbar_sop(2) <= '1';
   crossbar_eop(2) <= '0';
   wait until clk'event and clk = '1';
   crossbar_sop(2) <= '0';
   crossbar_eop(2) <= '1';
   wait until clk'event and clk = '1';

   wait;
end process;

packet3: process
begin
   crossbar_sop(3) <= '0';
   crossbar_eop(3) <= '0';

   if reset = '1' then
      wait until reset = '0';
   end if;

   wait until clk'event and clk = '1';

   crossbar_sop(3) <= '1';
   crossbar_eop(3) <= '0';
   wait until clk'event and clk = '1';
   crossbar_sop(3) <= '0';
   crossbar_eop(3) <= '0';
   
   wait until clk'event and clk = '1';
   wait until clk'event and clk = '1';
   wait until clk'event and clk = '1';
   wait until clk'event and clk = '1';
   
   wait until clk'event and clk = '1';
   crossbar_sop(3) <= '0';
   crossbar_eop(3) <= '1';
   
   wait until clk'event and clk = '1';
   crossbar_sop(3) <= '0';
   crossbar_eop(3) <= '0';

   wait until clk'event and clk = '1';
   wait until clk'event and clk = '1';
   wait until clk'event and clk = '1';
   wait until clk'event and clk = '1';
   wait until clk'event and clk = '1';
   wait until clk'event and clk = '1';
   wait until clk'event and clk = '1';
end process;

packet4: process
begin

   crossbar_sop(4) <= '0';
   crossbar_eop(4) <= '0';

   wait;
end process;

packet5: process
begin

   crossbar_sop(5) <= '0';
   crossbar_eop(5) <= '0';

   wait;
end process;

end architecture;

