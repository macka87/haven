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
use work.math_pack.all;
use work.ib_pkg.all; -- Internal Bus Package
use work.ib_sim_oper.all; -- Internal Bus Simulation Package
use work.cb_pkg.all;
use work.cb_sim_oper.all;


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
   constant UUT_BASE_ADDR    : std_logic_vector(31 downto 0) := X"11111100";
   constant UUT_LIMIT        : std_logic_vector(31 downto 0) := X"00000100"; -- 256 Byte
   constant UUT2_BASE_ADDR   : std_logic_vector(31 downto 0) := X"22222200";
   constant UUT2_LIMIT       : std_logic_vector(31 downto 0) := X"00000100"; -- 256 Byte

   
   constant clkper_50        : time    := 20 ns;
   constant clkper_100       : time    := 10 ns;
   constant reset_time       : time    := 100 * clkper_100;

-- -----------------------Testbench auxilarity signals-------------------------
     -- CLK_GEN Signals
     signal reset               : std_logic;
     signal clk                 : std_logic;
     signal cb_clk              : std_logic;
     signal clk_50_in           : std_logic;
     signal clk50               : std_logic;
     signal clk100              : std_logic;
     signal ib_clk              : std_logic;
     signal lock                : std_logic;

     -- Internal Bus 64 (IB_SIM)
     signal internal_bus64      : t_internal_bus64;
     signal control_bus         : t_control_bus;
     signal cb_switch_port1     : t_control_bus;
     signal cb_switch_port2     : t_control_bus;
     signal cb_enpoint_bm       : t_ibbm_64;

     -- Switch1 Map
     signal switch1_port1       : t_internal_bus64;
     signal switch1_port2       : t_internal_bus64;
     
     -- Slave endpoint signals
     signal ep_slave_wr         : t_ibmi_write64;
     signal ep_slave_rd         : t_ibmi_read64s;

     -- Master endpoint signals
     signal ep_master_wr        : t_ibmi_write64;
     signal ep_master_rd        : t_ibmi_read64s;

     -- IB_SIM component ctrl      
     signal ib_sim_ctrl         : t_ib_ctrl;
     signal ib_sim_strobe       : std_logic;
     signal ib_sim_busy         : std_logic;
     signal cb_sim_params       : t_cb_params;
     signal cb_sim_strobe       : std_logic;
     signal cb_sim_busy         : std_logic;
     
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
cb_clk <= clk100;

   
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
      DOWNSTREAM0_LIMIT  => UUT_LIMIT,
      -- Port 2 Address Space
      DOWNSTREAM1_BASE   => UUT2_BASE_ADDR, 
      DOWNSTREAM1_LIMIT  => UUT2_LIMIT
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

-- -----------------------Portmaping of tested component-----------------------
uut: entity work.IB_ENDPOINT
   generic map (
     LIMIT          => UUT_LIMIT
   )
   port map (
      -- Common Interface
      IB_CLK         => ib_clk,
      IB_RESET       => reset,

      -- Internal Bus Interface
      INTERNAL_BUS   => switch1_port1,
     
      -- User Component Interface
      WR             => ep_slave_wr,
      RD             => ep_slave_rd
   );

-- -----------------------Portmaping of memory --------------------------------
IBMI64MEM_U : entity work.IBMI64MEM
   generic map (
      SIZE           => 256, -- Size of memory in bytes
      BRAM_DISTMEM   => 0          -- 0 = BRAM / 1 = DISTMEM
    )
   port map (
      -- Common Interface
      CLK            => ib_clk,
      RESET          => reset,
      -- IBMI64 Interface
      IBMI_WRITE64   => ep_slave_wr, 
      IBMI_READ64    => ep_slave_rd 
   );


-- -----------------------Portmaping of tested component-----------------------
uut2: entity work.IB_ENDPOINT_MASTER
   generic map (
      LIMIT          => UUT2_LIMIT
   )
   port map (
      -- Common Interface
      IB_CLK         => ib_clk,
      IB_RESET       => reset,

      -- Internal Bus Interface
      INTERNAL_BUS   => switch1_port2,
     
      -- User Component Interface
      WR             => ep_master_wr,
      RD             => ep_master_rd,
     
      -- Busmaster
      BM             => cb_enpoint_bm
  );

-- -----------------------Portmaping of memory --------------------------------
IBMI64MEM2_U : entity work.IBMI64MEM
   generic map (
      SIZE           => 256,        -- Size of memory in bytes
      BRAM_DISTMEM   => 0           -- 0 = BRAM / 1 = DISTMEM
    )
   port map (
      -- Common Interface
      CLK            => ib_clk,
      RESET          => reset,
      -- IBMI64 Interface
      IBMI_WRITE64   => ep_master_wr, 
      IBMI_READ64    => ep_master_rd 
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


-- Control Bus Simulation Components ------------------------------------------
CB_SIM_U: entity work.CB_SIM
   port map (
      -- Common interface
      CB_RESET          => reset,
      CB_CLK            => cb_clk,

      -- Control Bus Interface
      PORT0             => control_bus,

      -- CB SIM interface
      CTRL              => cb_sim_params,
      STROBE            => cb_sim_strobe,
      BUSY              => cb_sim_busy
      );

-- Control Bus Switch ---------------------------------------------------------
CB_SWITCH_2P_U: entity work.cb_switch_2p
   port map (
      CB_CLK      => cb_clk,
      CB_RESET    => reset,

      -- upstream port
      PORT0       => control_bus,

      -- downstream
      PORT1       => cb_switch_port1,
      PORT2       => cb_switch_port2
   );
cb_switch_port2.down.dst_rdy_n <= '0';
cb_switch_port2.up.src_rdy_n   <= '1';

-- Control Bus Endpoint -------------------------------------------------------
CB2BM_ENDPOINT_U : entity work.CB2BM_ENDPOINT
   generic map (
      DATA_WIDTH     => 16,     -- Other than 16 is not supported
      SOURCE_ID      => "0000", -- Something like address, unique
      EMPTY_INTERVAL =>  4,     -- Resend info about buffer free space
      IN_BUF_SIZE    => 16,     -- Input buffer size, 0 for no buffer
      OUT_BUF_SIZE   => 16,     -- Output buffer size, 16-256
      OUT_BUF_MSGS   =>  4      -- Maximal number of output messages buffered
   )
   port map (
      CB_CLK        => cb_clk,
      CB_RESET      => reset,
      
      -- Control Bus interface
      CB            => cb_switch_port1,

      BM            => cb_enpoint_bm
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

-- ----------------------------------------------------------------------------
-- Support for cb_op
procedure cb_op(ctrl : in t_cb_params) is
begin
   wait until (CB_CLK'event and CB_CLK='1' and cb_sim_busy = '0');
   cb_sim_params <= ctrl;
   cb_sim_strobe <= '1';
   wait until (CB_CLK'event and CB_CLK='1');
   cb_sim_strobe <= '0';
end cb_op;

-- start testing ---------------------------------------------------------------
begin

   -- Testbench
   wait for reset_time;
   -- -------------------------
   -- Slave Endpoint Test START
   ----------------------------
   if (true) then 
     -- Write first 64 words and read it
     ib_op(ib_local_write(UUT_BASE_ADDR, X"00000000", 4, 16#ABAB#, '0', X"ABABABABABABABAB"));
     ib_op(ib_local_write(UUT_BASE_ADDR+4, X"00000000", 4, 16#ABAB#, '1', X"CDCDCDCDCDCDCDCD"));
     ib_op(ib_local_read(UUT_BASE_ADDR, X"00000002", 8, 16#ABAB#));
     ib_op(ib_local_write(UUT_BASE_ADDR+2, X"00000000", 4, 16#ABAB#, '0', X"EFEFEFEFEFEFEFEF"));
     ib_op(ib_local_read(UUT_BASE_ADDR, X"00000002", 8, 16#ABAB#));
     -- Completition transaction
     ib_op(ib_write_completition(X"11111111", X"00000000",  0, 16#0001#)); -- Test Only (no sense for slave_endpoint)
     ib_op(ib_read_completition(UUT_BASE_ADDR+8, X"00000000", 16, 16#0001#, "./tests/test_write0.txt"));
     ib_op(ib_local_read(UUT_BASE_ADDR+8, X"00000002", 16, 16#ABAB#));

     -- Fill whole memory
     ib_op(ib_local_write_file(UUT_BASE_ADDR, X"00000000", 256, 16#ABAB#, '0', "./tests/test_write0.txt"));
     ib_op(ib_local_read(UUT_BASE_ADDR, X"00000002", 256, 16#ABAB#));
   end if;
   -- -------------------------
   -- Slave Endpoint Test STOP
   ----------------------------

   -- --------------------------
   -- Master Endpoint Test START
   -- --------------------------
   if (true) then 

     -- Global to local read
     cb_op(cb_bm_packet(0, "0000", X"A01", conv_std_logic_vector(64, 12), UUT2_BASE_ADDR, X"FEDCBA9876543210"));
     wait for 500 ns;
     ib_op(ib_read_completition(UUT2_BASE_ADDR, X"00000000", 64, 16#A01#, "./tests/test_write0.txt"));

     -- Local to global write
     ib_op(ib_local_write_file(UUT2_BASE_ADDR, X"00000000", 64, 16#AAAA#, '0', "./tests/test_write0.txt"));
     cb_op(cb_bm_packet(0, "0011", X"A02",  conv_std_logic_vector(64, 12), UUT2_BASE_ADDR, X"FEDCBA9876543210"));
     wait for 500 ns;
     ib_op(ib_write_completition(UUT2_BASE_ADDR, X"00000000",  0, 16#A02#));

--      cb_op(cb_bm_packet(0, "0011", "101010101010", "000000100000", X"22222222", X"FEDCBA9876543210"));
--      ib_op(ib_local_read(UUT2_BASE_ADDR, X"00000002", 32, 16#ABAB#)); 
--      ib_op(ib_local_write_file(UUT2_BASE_ADDR, X"00000000", 64, 16#ABAB#, '0', "./tests/test_write0.txt"));
--      ib_op(ib_local_write_file(UUT2_BASE_ADDR, X"00000000", 64, 16#ABAB#, '1', "./tests/test_write0.txt"));
--      ib_op(ib_read_completition(UUT2_BASE_ADDR, X"00000000", 32, 16#0001#, "./tests/test_write0.txt"));
--      ib_op(ib_write_completition(UUT2_BASE_ADDR, X"00000000",  0, 16#0001#));
--      ib_op(ib_local_write_file(UUT2_BASE_ADDR, X"00000000", 64, 16#ABAB#, '0', "./tests/test_write0.txt"));
--      ib_op(ib_local_write(UUT2_BASE_ADDR, X"00000000",  8, 16#ABAB#, '1', X"ABABABABABABABAB"));
   end if;
   -- -------------------------
   -- Slave Endpoint Test STOP
   ----------------------------
   wait;
end process;


end architecture TESTBENCH_ARCH; 
