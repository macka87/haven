--
-- TESTBENCH.vhd: ptrn_match testbench
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
use work.ib_sim_oper.all; -- Internal Bus Simulation Package
use work.ib_bfm_pkg.all;  -- Internal Bus BFM Package

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
   constant clkper_50       : time := 20 ns;
   constant clkper_100      : time := 10 ns;
   constant reset_time      : time := 100 * clkper_100;


-- -----------------------Testbench auxilarity signals-------------------------
     -- CLK_GEN Signals
     signal reset             : std_logic;
     signal clk               : std_logic;
     signal clk_50_in         : std_logic;
     signal clk50             : std_logic;
     signal clk100            : std_logic;
     signal ib_clk            : std_logic;
     signal lock              : std_logic;

     -- Internal Bus 64 (IB_SIM)
     signal internal_bus64    : t_internal_bus64;
     signal internal_bus_bfm  : t_internal_bus64;
   
     -- IB_SIM component ctrl      
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
ib_clk <= clk100;
 

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

-- Internal Bus Bus Functional Model ------------------------------------------
IB_BFM_U : entity work.IB_BFM
   GENERIC MAP (
       MEMORY_SIZE => 1024
       )
   PORT MAP (
      CLK          => ib_clk,
      -- Internal Bus Interface
      IB           => internal_bus_bfm
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
   internal_bus64.DOWN.dst_rdy_n   <= '0';
   internal_bus_bfm.DOWN.dst_rdy_n <= '0';
   
   -- Testbench
   wait for reset_time;
   wait until (IB_CLK'event and IB_CLK='1');

   SendLocalWriteFile    (X"11111111", X"00000000", 4097, 16#ABAB#, "./tests/test_write0.txt",  IbCmd);
   SendLocalRead         (X"22222220", X"00000002",  8, 16#ABAB#,                             IbCmd);
   SendLocalWrite        (X"11111111", X"00000000",  8, 16#ABAB#, X"ABABABABABABABAB",        IbCmd);
   SendLocalWriteFile    (X"11111111", X"00000000", 33, 16#ABAB#, "./tests/test_write0.txt",  IbCmd);
   SendLocalWrite32      (X"11111111", X"00000000",  8, 16#ABAB#, X"ABABABAB",                IbCmd);
   SendLocalWriteFile32  (X"11111111", X"00000000", 28, 16#ABAB#, "./tests/test_write32.txt", IbCmd);

   SendCompletition           (X"11111111", X"00000000",  8, 16#ABAB#, X"ABABABABABABABAB",       IbCmd);
   SendCompletitionFile       (X"11111111", X"00000000", 31, 16#ABAB#, "./tests/test_write0.txt", IbCmd);
   SendNotLastCompletition    (X"11111111", X"00000000",  8, 16#ABAB#, X"ABABABABABABABAB",       IbCmd);
   SendNotLastCompletitionFile(X"11111111", X"00000000", 31, 16#ABAB#,  "./tests/test_write0.txt", IbCmd);

   
   if (false) then
   -- Write File 32
   ib_op(ib_local_write_file32(X"11111110", X"00000000", 0, 16#ABAB#, '0', "./tests/test_write32.txt"));

   -- Write without ack
   ib_op(ib_local_write_file(X"11111110", X"00000000", 0, 16#ABAB#, '0', "./tests/test_write0.txt"));
   ib_op(ib_local_write(X"11111110", X"00000000", 8, 16#ABAB#, '0', X"ABABABABABABABAB"));

   -- Write with ack
   ib_op(ib_local_write_file(X"11111110", X"00000000", 33, 16#ABAB#, '1', "./tests/test_write0.txt"));
   ib_op(ib_local_write(X"11111110", X"00000000", 8, 16#ABAB#, '1', X"ABABABABABABABAB"));

   -- Unaligned write
   ib_op(ib_local_write(X"11111111", X"00000000", 7, 16#ABAB#, '0', X"ABABABABABABABAB"));
   ib_op(ib_local_write_file(X"11111111", X"00000000", 31, 16#ABAB#, '0', "./tests/test_write0.txt"));

   -- Read Trans
   ib_op(ib_local_read(X"22222220", X"00000002", 8, 16#ABAB#));

   -- Normal Completition (with data)
   ib_op(ib_read_completition(X"22222222", X"00000000", 0, 16#ABAB#, "./tests/test_write0.txt"));

   -- Ack Completition (without data)
   ib_op(ib_write_completition(X"22222222", X"00000000", 0 , 16#ABAB#));
   end if;           

   wait;
end process;


end architecture TESTBENCH_arch; 
