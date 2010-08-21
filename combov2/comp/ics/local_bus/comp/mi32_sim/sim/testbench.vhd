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
architecture TESTBENCH_arch of TESTBENCH is


-- -----------------------Testbench constant-----------------------------------
   constant clkper_50       : time    := 20 ns;
   constant clkper_100      : time    := 10 ns;
   constant reset_time      : time    := 100 * clkper_100;
   constant UUT_BASE_ADDR   : std_logic_vector(31 downto 0) := X"11111111";
   constant UUT_LIMIT       : integer := 256;

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

     signal lb_mi32             : t_mi32;
 
     -- IB_SIM component ctrl      
     signal ib_sim_ctrl         : t_ib_ctrl;
     signal ib_sim_strobe       : std_logic;
     signal ib_sim_busy         : std_logic;
     signal drd_cnt             : std_logic_vector(31 downto 0);
     signal drdy_rd_pipe        : std_logic_vector(9 downto 0);
     signal ardy_pipe           : std_logic_vector(9 downto 0);
     signal drd_cnt_ce          : std_logic;
     
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

clk    <= clk100;
ib_clk <= clk100;
lb_clk <= clk100;
   

-- Internal Bus simulation component ------------------------------------------
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

   -- Testbench
   wait for reset_time;

   ib_op(ib_local_write(X"11111110", X"00000000", 4, 16#ABAB#, '0', X"ABABABABABABABAB"));
   ib_op(ib_local_write(X"11111110", X"00000000", 4, 16#ABAB#, '0', X"ABABABABABABABAB"));
   ib_op(ib_local_read(X"11111110", X"00000002", 32, 16#ABAB#));
   ib_op(ib_local_read(X"11111110", X"00000002", 32, 16#ABAB#));
   ib_op(ib_local_write_file(X"11111110", X"00000000", 64, 16#ABAB#, '0', "./tests/test_write0.txt"));
   wait;
end process;

------------------------------
-- READ TRANSACTION TESTING
------------------------------

lb_mi32.drd        <= drd_cnt;
lb_mi32.ardy       <= lb_mi32.rd or lb_mi32.wr;
--ardy <= ardy_pipe(2) and (rd or wr);
lb_mi32.drdy       <= lb_mi32.rd;
drd_cnt_ce <= lb_mi32.rd;
--drdy       <= rd and ardy;
--drd_cnt_ce <= rd and ardy;

pipedrdyp: process(RESET, CLK)
  begin
   if (RESET = '1') then
      drdy_rd_pipe(0) <= '0';
      drdy_rd_pipe(1) <= '0';
      drdy_rd_pipe(2) <= '0';
      drdy_rd_pipe(3) <= '0';
      drdy_rd_pipe(4) <= '0';
      drdy_rd_pipe(5) <= '0';
      drdy_rd_pipe(6) <= '0';
      drdy_rd_pipe(7) <= '0';
      drdy_rd_pipe(8) <= '0';
      drdy_rd_pipe(9) <= '0';
      ardy_pipe(0) <= '0';
      ardy_pipe(1) <= '0';
      ardy_pipe(2) <= '0';
      ardy_pipe(3) <= '0';
      ardy_pipe(4) <= '0';
      ardy_pipe(5) <= '0';
      ardy_pipe(6) <= '0';
      ardy_pipe(7) <= '0';
      ardy_pipe(8) <= '0';
      ardy_pipe(9) <= '0';
   elsif (CLK'event AND CLK = '1') then
      drdy_rd_pipe(0) <= lb_mi32.rd;
      drdy_rd_pipe(1) <= drdy_rd_pipe(0);
      drdy_rd_pipe(2) <= drdy_rd_pipe(1);
      drdy_rd_pipe(3) <= drdy_rd_pipe(2);
      drdy_rd_pipe(4) <= drdy_rd_pipe(3);
      drdy_rd_pipe(5) <= drdy_rd_pipe(4);
      drdy_rd_pipe(6) <= drdy_rd_pipe(5);
      drdy_rd_pipe(7) <= drdy_rd_pipe(6);
      drdy_rd_pipe(8) <= drdy_rd_pipe(7);
      drdy_rd_pipe(9) <= drdy_rd_pipe(8);

      ardy_pipe(0) <= lb_mi32.rd or lb_mi32.wr;
      ardy_pipe(1) <= ardy_pipe(0);
      ardy_pipe(2) <= ardy_pipe(1);
      ardy_pipe(3) <= ardy_pipe(2);
      ardy_pipe(4) <= ardy_pipe(3);
      ardy_pipe(5) <= ardy_pipe(4);
      ardy_pipe(6) <= ardy_pipe(5);
      ardy_pipe(7) <= ardy_pipe(6);
      ardy_pipe(8) <= ardy_pipe(7);
      ardy_pipe(9) <= ardy_pipe(8);
    end if;
end process;

-- drd_cnt counter
drd_cntp: process(RESET, CLK)
begin
   if (RESET = '1') then
      drd_cnt <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (drd_cnt_ce = '1') then
          drd_cnt <= drd_cnt + X"11111111";
       end if;
   end if;
end process;

end architecture TESTBENCH_arch; 
