--
-- TESTBENCH.vhd: ptrn_match testbench
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
--            Patrik Beck <beck@liberouter.org>
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
use work.cb_pkg.all; -- Control Bus Package
use work.cb_sim_oper.all; -- Control Bus Simulation Package

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
   
   constant NUMBER_SIM      : INTEGER := 6;
   constant DATA_WIDTH      : INTEGER := 16;


-- -----------------------Testbench auxilarity signals-------------------------
     -- CLK_GEN Signals
     signal reset             : std_logic;
     signal clk               : std_logic;
     signal clk_50_in         : std_logic;
     signal clk50             : std_logic;
     signal clk100            : std_logic;
     signal cb_clk            : std_logic;
     signal lock              : std_logic;

     -- Switch1 Map
     signal port0_in          : t_control_bus;
     signal port0_out         : t_control_bus; 
     signal sw1_ds_in         : std_logic_vector(2*(DATA_WIDTH + 3)-1 downto 0);
     signal sw1_ds_out        : std_logic_vector(2*(DATA_WIDTH + 3)-1 downto 0);
     signal sw1_ds_in_rd      : std_logic_vector(1 downto 0);
     signal sw1_ds_out_rd     : std_logic_vector(1 downto 0);
    
     -- Switch2 Map
     signal switch2_port0_in          : t_control_bus;
     signal switch2_port0_out         : t_control_bus;
     signal switch2_port1_in          : t_control_bus;
     signal switch2_port1_out         : t_control_bus;
     signal switch2_port2_in          : t_control_bus;
     signal switch2_port2_out         : t_control_bus;
   
     -- Switch3 Map
     signal switch3_port0_in          : t_control_bus;
     signal switch3_port0_out         : t_control_bus;
     signal sw3_ds_in                 : std_logic_vector(3*(DATA_WIDTH + 3)-1 downto 0);
     signal sw3_ds_out                : std_logic_vector(3*(DATA_WIDTH + 3)-1 downto 0);
     signal sw3_ds_in_rd              : std_logic_vector(3-1 downto 0);
     signal sw3_ds_out_rd             : std_logic_vector(3-1 downto 0);
 
     -- Simulation component
     type sim_port is array (0 to NUMBER_SIM-1) of t_control_bus;
     signal sim_in                    : sim_port;
     signal sim_out                   : sim_port;
 

     -- CB_SIM component ctrl      
     type a_t_cb_params is array (0 to NUMBER_SIM-1) of t_cb_params;
     signal cb_sim_params  : a_t_cb_params;
     signal cb_sim_strobe  : std_logic_vector(NUMBER_SIM-1 downto 0);
     signal cb_sim_busy    : std_logic_vector(NUMBER_SIM-1 downto 0);

   
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
cb_clk <= clk100;
   
-- -----------------------Portmaping of tested component-----------------------
uut1 : entity work.CB_SWITCH
   generic map (
      -- Data Width (64/128)
      DATA_WIDTH         => 16,
      DS_PORTS           => 2
  )

   port map (
      -- Common Interface
      CB_CLK             => cb_clk,
      CB_RESET           => reset,
      -- Port 0 (Upstream Port)
      PORT0_IN          => port0_in,
      PORT0_OUT         => port0_out,
      
      -- Downstream
      DS_IN          => sw1_ds_in,
      DS_IN_RD       => sw1_ds_in_rd,
      
      DS_OUT         => sw1_ds_out,
      DS_OUT_RD      => sw1_ds_out_rd
   );

-- -----------------------Portmaping of tested component-----------------------
uut2 : entity work.CB_SWITCH_2P
   generic map (
      DATA_WIDTH         => 16
  )

   port map (
      -- Common Interface
      CB_CLK             => cb_clk,
      CB_RESET           => reset,
      -- Port 0 (Upstream Port)
      PORT0_IN          => switch2_port0_in,
      PORT0_OUT         => switch2_port0_out,

      -- Downstream
      PORT1_IN          => sim_out(1),
      PORT1_OUT         => sim_in(1),
      
      PORT2_IN          => switch3_port0_out,
      PORT2_OUT         => switch3_port0_in
  );

-- -----------------------Portmaping of tested component-----------------------
uut3 : entity work.CB_SWITCH
   generic map (
      DATA_WIDTH         => 16,
      DS_PORTS           => 3  
   )

   port map (
      -- Common Interface
      CB_CLK             => cb_clk,
      CB_RESET           => reset,
      -- Port 0 (Upstream Port)
      PORT0_IN          => switch3_port0_in,
      PORT0_OUT         => switch3_port0_out,

      -- Downstream
      DS_IN          => sw3_ds_in,
      DS_IN_RD       => sw3_ds_in_rd,
      
      DS_OUT         => sw3_ds_out,
      DS_OUT_RD      => sw3_ds_out_rd
   );

                            
--------------------------------------------------------
-- switch switch connections

switch2_port0_in.data <= sw1_ds_out(2*(DATA_WIDTH + 3)-1 downto 2*(DATA_WIDTH + 3)-DATA_WIDTH);
switch2_port0_in.sop_n <= sw1_ds_out(2*(DATA_WIDTH + 3) - (DATA_WIDTH + 1));
switch2_port0_in.eop_n <= sw1_ds_out(2*(DATA_WIDTH + 3) - (DATA_WIDTH + 2));
switch2_port0_in.src_rdy_n <= sw1_ds_out(2*(DATA_WIDTH + 3) - (DATA_WIDTH + 3));
sw1_ds_out_rd(1) <= switch2_port0_in.dst_rdy_n;

sw1_ds_in(2*(DATA_WIDTH + 3)-1 downto 2*(DATA_WIDTH + 3)-DATA_WIDTH) <= switch2_port0_out.data;
sw1_ds_in(2*(DATA_WIDTH + 3) - (DATA_WIDTH + 1)) <= switch2_port0_out.sop_n;
sw1_ds_in(2*(DATA_WIDTH + 3) - (DATA_WIDTH + 2)) <= switch2_port0_out.eop_n;
sw1_ds_in(2*(DATA_WIDTH + 3) - (DATA_WIDTH + 3)) <= switch2_port0_out.src_rdy_n;
switch2_port0_out.dst_rdy_n <= sw1_ds_in_rd(1);

---------------------------------------------------------
-- switch sim connections

port0_in.data <= sim_out(4).data;
port0_in.sop_n <= sim_out(4).sop_n;
port0_in.eop_n <= sim_out(4).eop_n;
port0_in.src_rdy_n <= sim_out(4).src_rdy_n;
sim_out(4).dst_rdy_n <= port0_in.dst_rdy_n;

port0_out.dst_rdy_n <= sim_in(4).dst_rdy_n;


sw1_ds_in(1*(DATA_WIDTH + 3)-1 downto 1*(DATA_WIDTH + 3)-DATA_WIDTH) <= sim_out(0).data;
sw1_ds_in(1*(DATA_WIDTH + 3) - (DATA_WIDTH + 1)) <= sim_out(0).sop_n;
sw1_ds_in(1*(DATA_WIDTH + 3) - (DATA_WIDTH + 2)) <= sim_out(0).eop_n;
sw1_ds_in(1*(DATA_WIDTH + 3) - (DATA_WIDTH + 3)) <= sim_out(0).src_rdy_n;
sim_out(0).dst_rdy_n <= sw1_ds_in_rd(0);

sw1_ds_out_rd(0) <= sim_in(0).dst_rdy_n;

sw3_ds_in(1*(DATA_WIDTH + 3)-1 downto 1*(DATA_WIDTH + 3)-DATA_WIDTH) <= sim_out(2).data;
sw3_ds_in(1*(DATA_WIDTH + 3) - (DATA_WIDTH + 1)) <= sim_out(2).sop_n;
sw3_ds_in(1*(DATA_WIDTH + 3) - (DATA_WIDTH + 2)) <= sim_out(2).eop_n;
sw3_ds_in(1*(DATA_WIDTH + 3) - (DATA_WIDTH + 3)) <= sim_out(2).src_rdy_n;
sim_out(2).dst_rdy_n <= sw3_ds_in_rd(0);

sw3_ds_out_rd(0) <= sim_in(2).dst_rdy_n;

sw3_ds_in(2*(DATA_WIDTH + 3)-1 downto 2*(DATA_WIDTH + 3)-DATA_WIDTH) <= sim_out(3).data;
sw3_ds_in(2*(DATA_WIDTH + 3) - (DATA_WIDTH + 1)) <= sim_out(3).sop_n;
sw3_ds_in(2*(DATA_WIDTH + 3) - (DATA_WIDTH + 2)) <= sim_out(3).eop_n;
sw3_ds_in(2*(DATA_WIDTH + 3) - (DATA_WIDTH + 3)) <= sim_out(3).src_rdy_n;
sim_out(3).dst_rdy_n <= sw3_ds_in_rd(1);

sw3_ds_out_rd(1) <= sim_in(3).dst_rdy_n;

sw3_ds_in(3*(DATA_WIDTH + 3)-1 downto 3*(DATA_WIDTH + 3)-DATA_WIDTH) <= sim_out(5).data;
sw3_ds_in(3*(DATA_WIDTH + 3) - (DATA_WIDTH + 1)) <= sim_out(5).sop_n;
sw3_ds_in(3*(DATA_WIDTH + 3) - (DATA_WIDTH + 2)) <= sim_out(5).eop_n;
sw3_ds_in(3*(DATA_WIDTH + 3) - (DATA_WIDTH + 3)) <= sim_out(5).src_rdy_n;
sim_out(5).dst_rdy_n <= sw3_ds_in_rd(2);

sw3_ds_out_rd(2) <= sim_in(5).dst_rdy_n;


-- Internal Bus simulation component ------------------------------------------
SIM: for i in 0 to NUMBER_SIM-1 generate
   CB_SIM_U : entity work.CB_SIM
      port map (
         -- Common interface
         CB_RESET           => reset,
         CB_CLK             => cb_clk,

         -- Control Bus Interface
         PORT0_IN           => sim_in(i),
         PORT0_OUT          => sim_out(i),

         -- IB SIM interface
         CTRL               => cb_sim_params(i),
         STROBE             => cb_sim_strobe(i),
         BUSY               => cb_sim_busy(i)
         );

end generate;


tb : process


-- start testing ---------------------------------------------------------------
-- ----------------------------------------------------------------------------
-- Support for cb_op
procedure cb_op(ctrl : in t_cb_params) is
begin
   wait until (CB_CLK'event and CB_CLK='1' and cb_sim_busy(4) = '0');
   cb_sim_params(4) <= ctrl;
   cb_sim_strobe(4) <= '1';
   wait until (CB_CLK'event and CB_CLK='1');
   cb_sim_strobe(4) <= '0';
end cb_op;


begin

   wait for reset_time;

   --send packet from root
   cb_op(cb_packet(1, 1, X"AA01"));

   wait;
end process;

process
-- ----------------------------------------------------------------------------
-- Support for cb_op
procedure cb_op(ctrl : in t_cb_params) is
begin
   wait until (CB_CLK'event and CB_CLK='1' and cb_sim_busy(2) = '0');
   cb_sim_params(2) <= ctrl;
   cb_sim_strobe(2) <= '1';
   wait until (CB_CLK'event and CB_CLK='1');
   cb_sim_strobe(2) <= '0';
end cb_op;



begin
  
   wait for reset_time;
   wait for 20 * clkper_100;
  
   --send packets on port 1,2 switch 2
   cb_op(cb_packet(3, 3, X"AA03"));  --collision
   cb_op(cb_packet(5, 5, X"AA05"));  --collision 
   cb_op(cb_packet(7, 7, X"AA07"));  --collision 

   wait;
end process;

process
-- ----------------------------------------------------------------------------
-- Support for cb_op
procedure cb_op(ctrl : in t_cb_params) is
begin
   wait until (CB_CLK'event and CB_CLK='1' and cb_sim_busy(3) = '0');
   cb_sim_params(3) <= ctrl;
   cb_sim_strobe(3) <= '1';
   wait until (CB_CLK'event and CB_CLK='1');
   cb_sim_strobe(3) <= '0';
end cb_op;

begin
  
   wait for reset_time;
   wait for 20 * clkper_100;
  
   --send packets on port 1,2 switch 2
   cb_op(cb_packet(4, 4, X"AA04"));  --collision
   cb_op(cb_packet(6, 6, X"AA06"));  --collision 
   cb_op(cb_packet(8, 8, X"AA08"));  --collision 

  
   wait;
end process;

process
-- ----------------------------------------------------------------------------
-- Support for cb_op
procedure cb_op(ctrl : in t_cb_params) is
begin
   wait until (CB_CLK'event and CB_CLK='1' and cb_sim_busy(5) = '0');
   cb_sim_params(5) <= ctrl;
   cb_sim_strobe(5) <= '1';
   wait until (CB_CLK'event and CB_CLK='1');
   cb_sim_strobe(5) <= '0';
end cb_op;

begin
  
   wait for reset_time;
   wait for 20 * clkper_100;
  
   --send packets on port 1,2 switch 2
   cb_op(cb_packet(10, 10, X"AA0A"));  --collision
   cb_op(cb_packet(11, 11, X"AA0B"));  --collision 
   cb_op(cb_packet(12, 12, X"AA0C"));  --collision 

  
   wait;
end process;

end architecture TESTBENCH_arch; 
