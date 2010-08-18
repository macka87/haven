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
   constant clkper          : time := 10 ns;
   constant reset_time      : time := 10 * clkper;


-- -----------------------Testbench auxilarity signals-------------------------
     -- CLK_GEN Signals
   signal reset             : std_logic;
   signal clk               : std_logic;

   signal ib0_down_data       : std_logic_vector(63 downto 0);
   signal ib0_down_sop_n      : std_logic;
   signal ib0_down_eop_n      : std_logic;
   signal ib0_down_src_rdy_n  : std_logic;
   signal ib0_down_dst_rdy_n  : std_logic;
   signal ib0_up_data         : std_logic_vector(63 downto 0);
   signal ib0_up_sop_n        : std_logic;
   signal ib0_up_eop_n        : std_logic;
   signal ib0_up_src_rdy_n    : std_logic;
   signal ib0_up_dst_rdy_n    : std_logic;  

   signal ib1_down_data       : std_logic_vector(63 downto 0);
   signal ib1_down_sop_n      : std_logic;
   signal ib1_down_eop_n      : std_logic;
   signal ib1_down_src_rdy_n  : std_logic;
   signal ib1_down_dst_rdy_n  : std_logic;
   signal ib1_up_data         : std_logic_vector(63 downto 0);
   signal ib1_up_sop_n        : std_logic;
   signal ib1_up_eop_n        : std_logic;
   signal ib1_up_src_rdy_n    : std_logic;
   signal ib1_up_dst_rdy_n    : std_logic;  

   signal ib2_down_data       : std_logic_vector(63 downto 0);
   signal ib2_down_sop_n      : std_logic;
   signal ib2_down_eop_n      : std_logic;
   signal ib2_down_src_rdy_n  : std_logic;
   signal ib2_down_dst_rdy_n  : std_logic;
   signal ib2_up_data         : std_logic_vector(63 downto 0);
   signal ib2_up_sop_n        : std_logic;
   signal ib2_up_eop_n        : std_logic;
   signal ib2_up_src_rdy_n    : std_logic;
   signal ib2_up_dst_rdy_n    : std_logic;  

begin

-- Reset generation -----------------------------------------------------------
   reset_gen : process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process reset_gen;
   
-- clk generator ------------------------------------------------------------
clk_gen_p : process
begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
end process;

-- -----------------------Portmaping of tested component-----------------------
uut : entity work.IB_SWITCH_CORE
   generic map (
      -- Data Width (64/128)
      DATA_WIDTH         => 64,
      -- Port 0 Address Space
      SWITCH_BASE        => X"00000000",
      SWITCH_LIMIT       => X"C4000000",
      -- Port 1 Address Space
      DOWNSTREAM0_BASE   => X"00000000",
      DOWNSTREAM0_LIMIT  => X"02000000",
      -- Port 2 Address Space
      DOWNSTREAM1_BASE   => X"02000000", 
      DOWNSTREAM1_LIMIT  => X"C2000000"
   )

   port map (
      -- Common Interface
      IB_CLK         => clk,
      IB_RESET       => reset,
      -- Upstream Port
      PORT0_DOWN_DATA       => ib0_down_data,
      PORT0_DOWN_SOP_N      => ib0_down_sop_n,
      PORT0_DOWN_EOP_N      => ib0_down_eop_n,
      PORT0_DOWN_SRC_RDY_N  => ib0_down_src_rdy_n,
      PORT0_DOWN_DST_RDY_N  => ib0_down_dst_rdy_n,
      PORT0_UP_DATA         => ib0_up_data,
      PORT0_UP_SOP_N        => ib0_up_sop_n,
      PORT0_UP_EOP_N        => ib0_up_eop_n,
      PORT0_UP_SRC_RDY_N    => ib0_up_src_rdy_n,
      PORT0_UP_DST_RDY_N    => ib0_up_dst_rdy_n,
      -- Downstream Ports
      PORT1_DOWN_DATA       => ib1_down_data,
      PORT1_DOWN_SOP_N      => ib1_down_sop_n,
      PORT1_DOWN_EOP_N      => ib1_down_eop_n,
      PORT1_DOWN_SRC_RDY_N  => ib1_down_src_rdy_n,
      PORT1_DOWN_DST_RDY_N  => ib1_down_dst_rdy_n,
      PORT1_UP_DATA         => ib1_up_data,
      PORT1_UP_SOP_N        => ib1_up_sop_n,
      PORT1_UP_EOP_N        => ib1_up_eop_n,
      PORT1_UP_SRC_RDY_N    => ib1_up_src_rdy_n,
      PORT1_UP_DST_RDY_N    => ib1_up_dst_rdy_n,

      PORT2_DOWN_DATA       => ib2_down_data,
      PORT2_DOWN_SOP_N      => ib2_down_sop_n,
      PORT2_DOWN_EOP_N      => ib2_down_eop_n,
      PORT2_DOWN_SRC_RDY_N  => ib2_down_src_rdy_n,
      PORT2_DOWN_DST_RDY_N  => ib2_down_dst_rdy_n,
      PORT2_UP_DATA         => ib2_up_data,
      PORT2_UP_SOP_N        => ib2_up_sop_n,
      PORT2_UP_EOP_N        => ib2_up_eop_n,
      PORT2_UP_SRC_RDY_N    => ib2_up_src_rdy_n,
      PORT2_UP_DST_RDY_N    => ib2_up_dst_rdy_n
   );


tb : process
-- start testing ---------------------------------------------------------------
begin

   ib0_up_dst_rdy_n <= '0';
   ib0_down_data <= X"0000000000000000";
   ib0_down_sop_n <= '1';
   ib0_down_eop_n <= '1';
   ib0_down_src_rdy_n <= '1';

   ib1_up_data <= X"0000000000000000";
   ib1_up_sop_n <= '1';
   ib1_up_eop_n <= '1';
   ib1_up_src_rdy_n <= '1';
   ib1_down_dst_rdy_n <= '0';

   ib2_up_data <= X"0000000000000000";
   ib2_up_sop_n <= '1';
   ib2_up_eop_n <= '1';
   ib2_up_src_rdy_n <= '1';
   ib2_down_dst_rdy_n <= '0';

   reset <= '1';
   wait for reset_time;
   reset <= '0';

   wait for 10*clkper;

   ib0_down_src_rdy_n <= '0';
   ib0_down_data <= X"00000804000D1004";
   ib0_down_sop_n <= '0';
   wait for clkper;
   ib0_down_data <= X"00000000F0000000";
   ib0_down_sop_n <= '1';
   ib0_down_eop_n <= '0';
   wait for clkper;
   ib0_down_src_rdy_n <= '1';

   wait for 10*clkper;

   ib1_up_src_rdy_n <= '0';
   ib1_up_data <= X"F0000000000DD004";
   ib1_up_sop_n <= '0';
   wait for clkper;
   ib1_up_data <= X"0000000000000804";
   ib1_up_sop_n <= '1';
   wait for clkper;
   ib1_up_data <= X"0000000000000002";
   ib1_up_eop_n <= '0';
   wait for clkper;
   ib1_up_src_rdy_n <= '1';


   wait;
end process;


end architecture TESTBENCH_arch; 
