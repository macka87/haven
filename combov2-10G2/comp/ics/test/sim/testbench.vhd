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

use work.ib_pkg.all;
use work.lb_pkg.all;
use work.ib_sim_oper.all;
use work.ib_bfm_pkg.all;
use work.ics_test_app_pkg.all;
use work.ics_core_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity TESTBENCH is
end entity TESTBENCH;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture TESTBENCH_ARCH of TESTBENCH is

   constant MEMORY_BASE_ADDR : std_logic_vector(63 downto 0) := X"FFFFFFFF00000000";
   constant MEMORY_SIZE      : integer := 512;

-- -----------------------Testbench constant-----------------------------------
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
     signal top_level_clk       : std_logic;
     -- Internal Bus 64 (IB_SIM)
     signal internal_bus64      : t_internal_bus64;

     -- IB_SIM component ctrl      
     signal ib_sim_ctrl         : t_ib_ctrl;
     signal ib_sim_strobe       : std_logic;
     signal ib_sim_busy         : std_logic;
   
begin

top_level_clk <= ib_clk; -- after 1 ns;

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

-- -----------------------Portmaping of tested component-----------------------
uut: entity work.TOP_LEVEL
   port map (
      -- Common Interface
      CLK          => top_level_clk,
      RESET        => reset,
      
      -- Internal Bus Interface
      IB_DOWN_DATA        => internal_bus64.down.data,
      IB_DOWN_SOP_N       => internal_bus64.down.sop_n,
      IB_DOWN_EOP_N       => internal_bus64.down.eop_n,
      IB_DOWN_SRC_RDY_N   => internal_bus64.down.src_rdy_n,
      IB_DOWN_DST_RDY_N   => internal_bus64.down.dst_rdy_n,
      IB_UP_DATA          => internal_bus64.up.data,
      IB_UP_SOP_N         => internal_bus64.up.sop_n,
      IB_UP_EOP_N         => internal_bus64.up.eop_n,
      IB_UP_SRC_RDY_N     => internal_bus64.up.src_rdy_n,
      IB_UP_DST_RDY_N     => internal_bus64.up.dst_rdy_n
      );

-- Internal Bus simulation component ------------------------------------------
--IB_SIM_U : entity work.IB_SIM
--   generic map (
--      UPSTREAM_LOG_FILE   => "ib_upstream_log.txt",
--      DOWNSTREAM_LOG_FILE => "ib_downstream_log.txt"
--   )
--   port map (
--      -- Common interface
--      IB_RESET           => reset,
--      IB_CLK             => ib_clk,
--
--      -- Internal Bus Interface
--      INTERNAL_BUS       => internal_bus64,
--
--      -- IB SIM interface
--      CTRL               => ib_sim_ctrl,
--      STROBE             => ib_sim_strobe,
--      BUSY               => ib_sim_busy
--      );

-- Internal Bus simulation component ------------------------------------------
IB_BFM_U : entity work.IB_BFM
   generic map (
      MEMORY_SIZE      => MEMORY_SIZE,
      MEMORY_BASE_ADDR => MEMORY_BASE_ADDR
   )
   port map (
      -- Common interface
      CLK             => ib_clk,
      -- Internal Bus Interface
      IB              => internal_bus64
      );

tb : process
-- ----------------------------------------------------------------------------
--                                 Procedures declaration
-- ----------------------------------------------------------------------------
-- -- ----------------------------------------------------------------------------
-- -- Support for ib_op
-- procedure ib_op(ctrl : in t_ib_ctrl) is
-- begin
--    wait until (IB_CLK'event and IB_CLK='1' and ib_sim_busy = '0');
--    ib_sim_ctrl <= ctrl;
--    ib_sim_strobe <= '1';
--    wait until (IB_CLK'event and IB_CLK='1');
--    ib_sim_strobe <= '0';
-- end ib_op;

-- -- ----------------------------------------------------------------------------
-- -- Start busmaster operation
-- procedure start_bm(mi32tobm_addr : in std_logic_vector(31 downto 0);
--                    global_addr   : in std_logic_vector(63 downto 0);
--                    local_addr    : in std_logic_vector(31 downto 0);
--                    length        : in integer;
--                    tag           : in std_logic_vector(15 downto 0);
--                    trans_type    : in std_logic_vector(1 downto 0)) is
-- begin
--    ib_op(ib_local_write(mi32tobm_addr,    X"FFFFFFFF", 8, 16#B1B1#, '0', global_addr));
--    ib_op(ib_local_write(mi32tobm_addr+8,  X"FFFFFFFF", 8, 16#B1B1#, '0', conv_std_logic_vector(length, 32) & local_addr));
--    ib_op(ib_local_write(mi32tobm_addr+16, X"FFFFFFFF", 5, 16#B1B1#, '0',  X"0000000" & '0' & trans_type & '1' & X"0000" & tag));
-- end start_bm;

-- ----------------------------------------------------------------------------
-- Start busmaster operation
procedure start_bm(mi32tobm_addr : in std_logic_vector(31 downto 0);
                   global_addr   : in std_logic_vector(63 downto 0);
                   local_addr    : in std_logic_vector(31 downto 0);
                   length        : in integer;
                   tag           : in std_logic_vector(15 downto 0);
                   trans_type    : in std_logic_vector(1 downto 0)) is
begin
   SendLocalWrite(mi32tobm_addr,    X"FFFFFFFF", 8, 16#B1B1#, global_addr, IbCmd);
   SendLocalWrite(mi32tobm_addr+8,  X"FFFFFFFF", 8, 16#B1B1#, conv_std_logic_vector(length, 32) & local_addr, IbCmd);
   SendLocalWrite(mi32tobm_addr+16, X"FFFFFFFF", 5, 16#B1B1#, X"0000000" & '0' & trans_type & '1' & X"0000" & tag, IbCmd);
end start_bm;



-- start testing ---------------------------------------------------------------
begin
   wait for reset_time;

   -----------------------------------------------------------------------------
   -- Basic Read Write Testing
   -- --------------------------------------------------------------------------
   if (false) then 
     wait until (IB_CLK'event and IB_CLK='1');
     -- Write data to IB endpoints
     SendLocalWrite(IB_USER0_BASE, X"FFFFFFFF", 8, 16#0001#, X"1F1F1F1F1F1F1F1F", IbCmd);
     SendLocalWrite(IB_USER1_BASE, X"FFFFFFFF", 8, 16#0002#, X"2F2F2F2F2F2F2F2F", IbCmd);
     SendLocalWrite(IB_USER2_BASE, X"FFFFFFFF", 8, 16#0003#, X"3F3F3F3F3F3F3F3F", IbCmd);
     SendLocalWrite(IB_USER3_BASE, X"FFFFFFFF", 8, 16#0004#, X"4F4F4F4F4F4F4F4F", IbCmd);
     -- Write data to LB endpoints
     SendLocalWrite(LB_USER0_BASE, X"FFFFFFFF", 8, 16#0005#, X"5F5F5F5F5F5F5F5F", IbCmd);
     SendLocalWrite(LB_USER1_BASE, X"FFFFFFFF", 8, 16#0006#, X"6F6F6F6F6F6F6F6F", IbCmd);
     SendLocalWrite(LB_USER2_BASE, X"FFFFFFFF", 8, 16#0007#, X"7F7F7F7F7F7F7F7F", IbCmd);
     SendLocalWrite(LB_USER3_BASE, X"FFFFFFFF", 8, 16#0008#, X"8F8F8F8F8F8F8F8F", IbCmd);
     SendLocalWrite(LB_USER4_BASE, X"FFFFFFFF", 8, 16#0009#, X"9F9F9F9F9F9F9F9F", IbCmd);
     SendLocalWrite(LB_USER5_BASE, X"FFFFFFFF", 8, 16#000A#, X"AFAFAFAFAFAFAFAF", IbCmd);
     --SendLocalWrite(LB_USER6_BASE, X"FFFFFFFF", 8, 16#000B#, X"BFBFBFBFBFBFBFBF", IbCmd);

     -- Read data to IB endpoints
     SendLocalRead(IB_USER0_BASE, X"FFFFFFFF", 8, 16#0001#, IbCmd);
     SendLocalRead(IB_USER1_BASE, X"FFFFFFFF", 8, 16#0002#, IbCmd);
     SendLocalRead(IB_USER2_BASE, X"FFFFFFFF", 8, 16#0003#, IbCmd);
     SendLocalRead(IB_USER3_BASE, X"FFFFFFFF", 8, 16#0004#, IbCmd);
     -- Read data to LB endpoints
     SendLocalRead(LB_USER0_BASE, X"FFFFFFFF", 8, 16#0005#, IbCmd);
     SendLocalRead(LB_USER1_BASE, X"FFFFFFFF", 8, 16#0006#, IbCmd);
     SendLocalRead(LB_USER2_BASE, X"FFFFFFFF", 8, 16#0007#, IbCmd);
     SendLocalRead(LB_USER3_BASE, X"FFFFFFFF", 8, 16#0008#, IbCmd);
     SendLocalRead(LB_USER4_BASE, X"FFFFFFFF", 8, 16#0009#, IbCmd);
     SendLocalRead(LB_USER5_BASE, X"FFFFFFFF", 8, 16#000A#, IbCmd);
     --SendLocalRead(LB_USER6_BASE, X"FFFFFFFF", 8, 16#000B#, IbCmd);

     -- Write data to IB endpoints (Testing BE)
     SendLocalWrite(IB_USER0_BASE+2, X"FFFFFFFF", 4, 16#0001#, X"0000000011111111", IbCmd);
     SendLocalWrite(IB_USER1_BASE+2, X"FFFFFFFF", 4, 16#0002#, X"0000000022222222", IbCmd);
     SendLocalWrite(IB_USER2_BASE+2, X"FFFFFFFF", 4, 16#0003#, X"0000000033333333", IbCmd);
     SendLocalWrite(IB_USER3_BASE+2, X"FFFFFFFF", 4, 16#0004#, X"0000000044444444", IbCmd);
     -- Write data to LB endpoints (Testing BE)
     SendLocalWrite(LB_USER0_BASE+2, X"FFFFFFFF", 4, 16#0005#, X"0000000055555555", IbCmd);
     SendLocalWrite(LB_USER1_BASE+2, X"FFFFFFFF", 4, 16#0006#, X"0000000066666666", IbCmd);
     SendLocalWrite(LB_USER2_BASE+2, X"FFFFFFFF", 4, 16#0007#, X"0000000077777777", IbCmd);
     SendLocalWrite(LB_USER3_BASE+2, X"FFFFFFFF", 4, 16#0008#, X"0000000088888888", IbCmd);
     SendLocalWrite(LB_USER4_BASE+2, X"FFFFFFFF", 4, 16#0009#, X"0000000099999999", IbCmd);
     SendLocalWrite(LB_USER5_BASE+2, X"FFFFFFFF", 4, 16#000A#, X"00000000AAAAAAAA", IbCmd);
     --SendLocalWrite(LB_USER6_BASE+2, X"FFFFFFFF", 4, 16#000B#, '0', X"00000000BBBBBBBB"));

     -- Read data to IB endpoints (Testing BE)
     SendLocalRead(IB_USER0_BASE, X"FFFFFFFF", 8, 16#0001#, IbCmd);
     SendLocalRead(IB_USER1_BASE, X"FFFFFFFF", 8, 16#0002#, IbCmd);
     SendLocalRead(IB_USER2_BASE, X"FFFFFFFF", 8, 16#0003#, IbCmd);
     SendLocalRead(IB_USER3_BASE, X"FFFFFFFF", 8, 16#0004#, IbCmd);
     -- Read data to LB endpoints (Testing BE)
     SendLocalRead(LB_USER0_BASE, X"FFFFFFFF", 8, 16#0005#, IbCmd);
     SendLocalRead(LB_USER1_BASE, X"FFFFFFFF", 8, 16#0006#, IbCmd);
     SendLocalRead(LB_USER2_BASE, X"FFFFFFFF", 8, 16#0007#, IbCmd);
     SendLocalRead(LB_USER3_BASE, X"FFFFFFFF", 8, 16#0008#, IbCmd);
     SendLocalRead(LB_USER4_BASE, X"FFFFFFFF", 8, 16#0009#, IbCmd);
     SendLocalRead(LB_USER5_BASE, X"FFFFFFFF", 8, 16#000A#, IbCmd);
     --SendLocalRead(LB_USER6_BASE, X"FFFFFFFF", 8, 16#000B#, IbCmd);
     wait for 3000 ns; -- Wait for finnishing all transactions
  end if;

  -----------------------------------------------------------------------------
  -- Busmaster Testing
  -- --------------------------------------------------------------------------
  if (true) then 
    wait until (IB_CLK'event and IB_CLK='1');

    -- ----------------------------------------
    -- Disable Transcript Logging
    -- SetTranscriptLogging(false, IbCmd);
    -- ----------------------------------------
    -- Enable File Logging
    -- SetFileLogging(true, IbCmd);
    -------------------------------------------
    -- Init Memory with Data from File
    -- InitMemory(32, "./tests/test_write0.txt", IbCmd);
    -------------------------------------------
    -- Show Host Memory Content
    -- ShowMemory(IbCmd);

    -------------------------------------------------------------
    REPORT LF & LF & LF & "Local 2 Global Write Test START" & LF & LF SEVERITY NOTE;
    -- Init FPGA Component Memory
    SendLocalWriteFile(IB_USER3_BASE, X"FFFFFFFF", 64, 16#0001#, "./tests/test_write0.txt", IbCmd);

    -- Send BM Request
    -- Start Local 2 Global Write Busmaster Transaction
    -- MI32TOBM_BASE, GLOBAL_ADDR, LOCAL_ADDR, LENGTH, TAG, TYPE
    start_bm(LB_USER6_BASE, MEMORY_BASE_ADDR, IB_USER3_BASE, 64, X"FFF1", "01");

    wait for 1001 ns; -- Wait for BM
    -- Show Host Memory Content
    ShowMemory(IbCmd);
    REPORT "Local 2 Global Write Test END" SEVERITY NOTE;
    ------------------------------------------------------------

    -------------------------------------------------------------
    REPORT LF & LF & LF & "Global 2 Local Read Test START" & LF & LF SEVERITY NOTE;
    -- Init FPGA Component from Memory
    
    -- Start Global 2 Local Read Busmaster Transaction
    -- MI32TOBM_BASE, GLOBAL_ADDR, LOCAL_ADDR, LENGTH, TAG, TYPE
    start_bm(LB_USER6_BASE, MEMORY_BASE_ADDR, IB_USER2_BASE, 32, X"FFF2", "00");
    
    wait for 1001 ns; -- Wait for BM
        -- Read Data from Component
    SendLocalRead(IB_USER2_BASE, X"FFFFFFFF", 32, 16#0005#, IbCmd);
    wait for 1001 ns; -- Wait for Compl
    -------------------------------------------------------------
    REPORT LF & LF & LF & "Global 2 Local Read Test END" SEVERITY NOTE;

  end if;


--    -- Testbench
--    wait for reset_time;
--    -- Mini App testing
--    if (false) then
--      -- Write data to IB endpoints
--      ib_op(ib_local_write(IB_USER0_BASE, X"FFFFFFFF", 8, 16#0001#, '0', X"1F1F1F1F1F1F1F1F"));
--      -- Write data to LB endpoints
--      ib_op(ib_local_write(LB_USER0_BASE, X"FFFFFFFF", 8, 16#0005#, '0', X"5F5F5F5F5F5F5F5F"));
--      -- Read data to IB endpoints
--      ib_op(ib_local_read(IB_USER0_BASE, X"FFFFFFFF", 8, 16#0001#));
--      -- Read data to LB endpoints
--      ib_op(ib_local_read(LB_USER0_BASE, X"FFFFFFFF", 8, 16#0005#));
-- 
--      -- Write data to IB endpoints (Testing BE)
--      ib_op(ib_local_write(IB_USER0_BASE+2, X"FFFFFFFF", 4, 16#0001#, '0', X"0000000011111111"));
--      -- Write data to LB endpoints (Testing BE)
--      ib_op(ib_local_write(LB_USER0_BASE+2, X"FFFFFFFF", 4, 16#0005#, '0', X"0000000055555555"));
--      -- Read data to IB endpoints (Testing BE)
--      ib_op(ib_local_read(IB_USER0_BASE, X"FFFFFFFF", 8, 16#0001#));
--      -- Read data to LB endpoints (Testing BE)
--      ib_op(ib_local_read(LB_USER0_BASE, X"FFFFFFFF", 8, 16#0005#));
--      wait for 3000 ns; -- Wait for finnishing all transactions
--    end if;
-- 
--    -- Normal App testing
--    if (true) then 
--      -- Write data to IB endpoints
--      ib_op(ib_local_write(IB_USER0_BASE, X"FFFFFFFF", 8, 16#0001#, '0', X"1F1F1F1F1F1F1F1F"));
--      ib_op(ib_local_write(IB_USER1_BASE, X"FFFFFFFF", 8, 16#0002#, '0', X"2F2F2F2F2F2F2F2F"));
--      ib_op(ib_local_write(IB_USER2_BASE, X"FFFFFFFF", 8, 16#0003#, '0', X"3F3F3F3F3F3F3F3F"));
--      ib_op(ib_local_write(IB_USER3_BASE, X"FFFFFFFF", 8, 16#0004#, '0', X"4F4F4F4F4F4F4F4F"));
--      -- Write data to LB endpoints
--      ib_op(ib_local_write(LB_USER0_BASE, X"FFFFFFFF", 8, 16#0005#, '0', X"5F5F5F5F5F5F5F5F"));
--      ib_op(ib_local_write(LB_USER1_BASE, X"FFFFFFFF", 8, 16#0006#, '0', X"6F6F6F6F6F6F6F6F"));
--      ib_op(ib_local_write(LB_USER2_BASE, X"FFFFFFFF", 8, 16#0007#, '0', X"7F7F7F7F7F7F7F7F"));
--      ib_op(ib_local_write(LB_USER3_BASE, X"FFFFFFFF", 8, 16#0008#, '0', X"8F8F8F8F8F8F8F8F"));
--      ib_op(ib_local_write(LB_USER4_BASE, X"FFFFFFFF", 8, 16#0009#, '0', X"9F9F9F9F9F9F9F9F"));
--      ib_op(ib_local_write(LB_USER5_BASE, X"FFFFFFFF", 8, 16#000A#, '0', X"AFAFAFAFAFAFAFAF"));
--      --ib_op(ib_local_write(LB_USER6_BASE, X"FFFFFFFF", 8, 16#000B#, '0', X"BFBFBFBFBFBFBFBF"));
-- 
--      -- Read data to IB endpoints
--      ib_op(ib_local_read(IB_USER0_BASE, X"FFFFFFFF", 8, 16#0001#));
--      ib_op(ib_local_read(IB_USER1_BASE, X"FFFFFFFF", 8, 16#0002#));
--      ib_op(ib_local_read(IB_USER2_BASE, X"FFFFFFFF", 8, 16#0003#));
--      ib_op(ib_local_read(IB_USER3_BASE, X"FFFFFFFF", 8, 16#0004#));
--      -- Read data to LB endpoints
--      ib_op(ib_local_read(LB_USER0_BASE, X"FFFFFFFF", 8, 16#0005#));
--      ib_op(ib_local_read(LB_USER1_BASE, X"FFFFFFFF", 8, 16#0006#));
--      ib_op(ib_local_read(LB_USER2_BASE, X"FFFFFFFF", 8, 16#0007#));
--      ib_op(ib_local_read(LB_USER3_BASE, X"FFFFFFFF", 8, 16#0008#));
--      ib_op(ib_local_read(LB_USER4_BASE, X"FFFFFFFF", 8, 16#0009#));
--      ib_op(ib_local_read(LB_USER5_BASE, X"FFFFFFFF", 8, 16#000A#));
--      --ib_op(ib_local_read(LB_USER6_BASE, X"FFFFFFFF", 8, 16#000B#));
-- 
--      -- Write data to IB endpoints (Testing BE)
--      ib_op(ib_local_write(IB_USER0_BASE+2, X"FFFFFFFF", 4, 16#0001#, '0', X"0000000011111111"));
--      ib_op(ib_local_write(IB_USER1_BASE+2, X"FFFFFFFF", 4, 16#0002#, '0', X"0000000022222222"));
--      ib_op(ib_local_write(IB_USER2_BASE+2, X"FFFFFFFF", 4, 16#0003#, '0', X"0000000033333333"));
--      ib_op(ib_local_write(IB_USER3_BASE+2, X"FFFFFFFF", 4, 16#0004#, '0', X"0000000044444444"));
--      -- Write data to LB endpoints (Testing BE)
--      ib_op(ib_local_write(LB_USER0_BASE+2, X"FFFFFFFF", 4, 16#0005#, '0', X"0000000055555555"));
--      ib_op(ib_local_write(LB_USER1_BASE+2, X"FFFFFFFF", 4, 16#0006#, '0', X"0000000066666666"));
--      ib_op(ib_local_write(LB_USER2_BASE+2, X"FFFFFFFF", 4, 16#0007#, '0', X"0000000077777777"));
--      ib_op(ib_local_write(LB_USER3_BASE+2, X"FFFFFFFF", 4, 16#0008#, '0', X"0000000088888888"));
--      ib_op(ib_local_write(LB_USER4_BASE+2, X"FFFFFFFF", 4, 16#0009#, '0', X"0000000099999999"));
--      ib_op(ib_local_write(LB_USER5_BASE+2, X"FFFFFFFF", 4, 16#000A#, '0', X"00000000AAAAAAAA"));
--      --ib_op(ib_local_write(LB_USER6_BASE+2, X"FFFFFFFF", 4, 16#000B#, '0', X"00000000BBBBBBBB"));
-- 
--      -- Read data to IB endpoints (Testing BE)
--      ib_op(ib_local_read(IB_USER0_BASE, X"FFFFFFFF", 8, 16#0001#));
--      ib_op(ib_local_read(IB_USER1_BASE, X"FFFFFFFF", 8, 16#0002#));
--      ib_op(ib_local_read(IB_USER2_BASE, X"FFFFFFFF", 8, 16#0003#));
--      ib_op(ib_local_read(IB_USER3_BASE, X"FFFFFFFF", 8, 16#0004#));
--      -- Read data to LB endpoints (Testing BE)
--      ib_op(ib_local_read(LB_USER0_BASE, X"FFFFFFFF", 8, 16#0005#));
--      ib_op(ib_local_read(LB_USER1_BASE, X"FFFFFFFF", 8, 16#0006#));
--      ib_op(ib_local_read(LB_USER2_BASE, X"FFFFFFFF", 8, 16#0007#));
--      ib_op(ib_local_read(LB_USER3_BASE, X"FFFFFFFF", 8, 16#0008#));
--      ib_op(ib_local_read(LB_USER4_BASE, X"FFFFFFFF", 8, 16#0009#));
--      ib_op(ib_local_read(LB_USER5_BASE, X"FFFFFFFF", 8, 16#000A#));
--      --ib_op(ib_local_read(LB_USER6_BASE, X"FFFFFFFF", 8, 16#000B#));
--      wait for 3000 ns; -- Wait for finnishing all transactions
--    end if;
--  
--    if (true) then 
--      -- Start Local 2 Global Write Busmaster Transaction
--      -- MI32TOBM_BASE, GLOBAL_ADDR, LOCAL_ADDR, LENGTH, TAG, TYPE
--      start_bm(LB_USER6_BASE, X"0123456789ABCDEF", IB_USER3_BASE, 16, X"FFF1", "01");
--      wait for 500 ns; --TODO: Change to waitig for incoming BM
--      ib_op(ib_write_completition(IB_USER3_BASE, X"FFFFFFFF", 16, 16#FFF1#));
-- 
--      -- Start Global 2 Local Read Busmaster Transaction
--      -- MI32TOBM_BASE, GLOBAL_ADDR, LOCAL_ADDR, LENGTH, TAG, TYPE
--      start_bm(LB_USER6_BASE, X"0123456789ABCDEF", IB_USER3_BASE, 16, X"FFF2", "00");
--      wait for 500 ns; --TODO: Change to waitig for incoming BM
--      ib_op(ib_read_completition(IB_USER3_BASE, X"FFFFFFFF", 16, 16#FFF2#, "./tests/test_write0.txt"));
-- 
--      -- Start Local 2 Global Write Busmaster Transaction
--      -- MI32TOBM_BASE, GLOBAL_ADDR, LOCAL_ADDR, LENGTH, TAG, TYPE
--      start_bm(LB_USER6_BASE, X"0123456789ABCDEF", IB_USER3_BASE, 16, X"FFF3", "01");
--      wait for 500 ns; --TODO: Change to waitig for incoming BM
--      ib_op(ib_write_completition(IB_USER3_BASE, X"FFFFFFFF", 16, 16#FFF3#));
--    end if;
-- 
--    -- Component busmaster testing
--    if (false) then 
--      ib_op(ib_local_write(IB_USER3_BASE, X"FFFFFFFF", 8, 16#0004#, '0', X"4F4F4F4F4F4F4F4F"));
-- 
--      -- Start Local 2 Local Write Busmaster Transaction
--      -- MI32TOBM_BASE, GLOBAL_ADDR, LOCAL_ADDR, LENGTH, TAG, TYPE
--      start_bm(LB_USER6_BASE, X"00000000" & IB_USER2_BASE, IB_USER3_BASE, 16, X"FFF1", "11");
--      wait for 500 ns; --TODO: Change to waitig for incoming BM
--    
--      -- Start Local 2 Local Read Busmaster Transaction
--      -- MI32TOBM_BASE, GLOBAL_ADDR, LOCAL_ADDR, LENGTH, TAG, TYPE
--      start_bm(LB_USER6_BASE, X"00000000" & IB_USER2_BASE, IB_USER3_BASE, 16, X"FFF2", "10");
--      wait for 500 ns; --TODO: Change to waitig for incoming BM
--    
--      -- Start Local 2 Global Write Busmaster Transaction
--      -- MI32TOBM_BASE, GLOBAL_ADDR, LOCAL_ADDR, LENGTH, TAG, TYPE
--      start_bm(LB_USER6_BASE, X"00000000" & IB_USER2_BASE, IB_USER3_BASE, 16, X"FFF3", "11");
--      wait for 500 ns; --TODO: Change to waitig for incoming BM
--    end if;
-- 
  wait;
end process;


end architecture TESTBENCH_ARCH; 
