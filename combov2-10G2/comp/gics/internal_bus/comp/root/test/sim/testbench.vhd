--
-- TESTBENCH.vhd: testbench
-- Copyright (C) 2008 CESNET
-- Author(s): Pavol Korcek <korcek@liberouter.org>
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
use work.ib_bfm_pkg.all;
use work.dma_test_pkg.all;

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
   constant MEMORY_SIZE      : integer := 16384;

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

   clk    <= clk100;
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
     -- Write data to memory
     SendLocalWrite(DOWNSTREAM1_BASE,     X"FFFFFFFF", 8, 16#0001#, X"1F1F1F1F1F1F1F1F", IbCmd);
     SendLocalWrite(DOWNSTREAM1_BASE+8,   X"FFFFFFFF", 8, 16#0002#, X"2F2F2F2F2F2F2F2F", IbCmd);
     SendLocalWrite(DOWNSTREAM1_BASE+16,  X"FFFFFFFF", 8, 16#0003#, X"3F3F3F3F3F3F3F3F", IbCmd);
     SendLocalWrite(DOWNSTREAM1_BASE+24,  X"FFFFFFFF", 8, 16#0004#, X"4F4F4F4F4F4F4F4F", IbCmd);
     -- Read data back
     SendLocalRead(DOWNSTREAM1_BASE+24,   X"FFFFFFFF", 8, 16#0005#, IbCmd);
     SendLocalRead(DOWNSTREAM1_BASE+16,   X"FFFFFFFF", 8, 16#0006#, IbCmd);
     SendLocalRead(DOWNSTREAM1_BASE+8,    X"FFFFFFFF", 8, 16#0007#, IbCmd);
     SendLocalRead(DOWNSTREAM1_BASE,      X"FFFFFFFF", 8, 16#0008#, IbCmd);
     wait for 3000 ns; -- Wait for finnishing all transactions
  end if;
  
   -----------------------------------------------------------------------------
   -- More Data Read Write Testing
   -- --------------------------------------------------------------------------
   if (false) then 
     wait until (IB_CLK'event and IB_CLK='1');
     -- Show memory in FPGA
     SendLocalRead(DOWNSTREAM1_BASE,   X"FFFFFFFF", 16, 16#0001#, IbCmd);
     -- Write data to memory
     SendLocalWriteFile(DOWNSTREAM1_BASE, X"FFFFFFFF", 16, 16#0002#, "./data/data0.txt", IbCmd);
     -- Read data back
     SendLocalRead(DOWNSTREAM1_BASE,   X"FFFFFFFF", 16, 16#0003#, IbCmd);
     wait for 3000 ns; -- Wait for finnishing all transactions
   end if; 
  -----------------------------------------------------------------------------
  -- Busmaster Testing
  -- --------------------------------------------------------------------------
  if (false) then 
   wait until (IB_CLK'event and IB_CLK='1');
   -- ----------------------------------------
   -- Disable Transcript Logging
   -- SetTranscriptLogging(false, IbCmd);
   -- ----------------------------------------
   -- Enable File Logging
   -- SetFileLogging(true, IbCmd);
    
   -------------------------------------------------------------
   REPORT LF & LF & LF & "Local 2 Global Write Test START" & LF & LF SEVERITY NOTE; 
       
   -- Show Host Memory Content
   ShowMemory(IbCmd);
    
   -- Init FPGA memory
   SendLocalWriteFile(DOWNSTREAM1_BASE, X"FFFFFFFF", 256, 16#0001#, "./data/data0.txt", IbCmd);

   -- Send BM Request
   -- Start Local 2 Global Write Busmaster Transaction
   -- MI32TOBM_BASE, GLOBAL_ADDR, LOCAL_ADDR, LENGTH, TAG, TYPE
   start_bm(LB_EP_BASE_ADDR, MEMORY_BASE_ADDR, DOWNSTREAM1_BASE, 256, X"FFF1", "01");
    
   wait for 1000 ns; -- Wait for BM
   ShowMemory(IbCmd);
 
   REPORT "Local 2 Global Write Test END" SEVERITY NOTE;
   ------------------------------------------------------------
   ------------------------------------------------------------
   REPORT LF & LF & LF & "Global 2 Local Read Test START" & LF & LF SEVERITY NOTE;

   -- Send BM Request
   -- Start Global 2 Local Read Busmaster Transaction
   -- MI32TOBM_BASE, GLOBAL_ADDR, LOCAL_ADDR, LENGTH, TAG, TYPE
   start_bm(LB_EP_BASE_ADDR, MEMORY_BASE_ADDR, DOWNSTREAM1_BASE, 256, X"FFF2", "00");
   
   wait for 1000 ns; -- Wait for BM

   -- Show memory in FPGA
   SendLocalRead(DOWNSTREAM1_BASE,   X"FFFFFFFF", 256, 16#0001#, IbCmd);
    
   wait for 1001 ns; -- Wait for Compl
   -------------------------------------------------------------
   REPORT LF & LF & LF & "Global 2 Local Read Test END" SEVERITY NOTE;
    
  end if;

  -----------------------------------------------------------------------------
  -- Busmaster Throughput Testing 
  --     (LB2BM in Modules.tcl have to be changed to LB2BM_throughput !!!)
  -- --------------------------------------------------------------------------
  if (true) then 
   wait until (IB_CLK'event and IB_CLK='1');
   -- ----------------------------------------
   -- Disable Transcript Logging
   -- SetTranscriptLogging(false, IbCmd);
   -- ----------------------------------------
   -- Enable File Logging
   -- SetFileLogging(true, IbCmd);

   -- Init FPGA memory
   SendLocalWriteFile(DOWNSTREAM1_BASE, X"FFFFFFFF", 256, 16#0001#, "./data/data0.txt", IbCmd);

   REPORT LF & LF & LF & "1.Throughput user initialization START" SEVERITY NOTE;

   -- read number of cycles (have to be 0 at beginning!)
   -- SendLocalRead(LB_EP_BASE_ADDR+24,    X"FFFFFFFF", 8, 16#0002#, IbCmd);

   -- init number of requests
   SendLocalWrite(LB_EP_BASE_ADDR+24, X"FFFFFFFF", 8, 16#FFEE#, X"0000000000000010", IbCmd);

   -- start whole G2L Bus Master operation -> invoke more BM transfers depending on req_reg
   start_bm(LB_EP_BASE_ADDR, MEMORY_BASE_ADDR, DOWNSTREAM1_BASE, 128, X"0003", "00");

   -- start whole L2G Bus Master operation -> invoke more BM transfers depending on req_reg
   start_bm(LB_EP_BASE_ADDR, MEMORY_BASE_ADDR, DOWNSTREAM1_BASE, 128, X"0001", "01");

   REPORT LF & LF & LF & "1.Throughput user initialization END" SEVERITY NOTE;

   -- wait for all dma transfers
   wait for 20 ms;

   REPORT LF & LF & LF & "1.Number of test cycles: - START" SEVERITY NOTE;

   wait until (IB_CLK'event and IB_CLK='1');

   -- read number of cycles (have to be more than 0!)
   SendLocalRead(LB_EP_BASE_ADDR+24,    X"FFFFFFFF", 8, 16#0006#, IbCmd); 

   -- wait for read answer
   wait for 1000 ns;

   REPORT LF & LF & LF & "1.Number of test cycles: - END" SEVERITY NOTE;

   -- *******************************************************************
   -- ************************* next test *******************************
   -- *******************************************************************

--    -- Init FPGA memory
--    SendLocalWriteFile(DOWNSTREAM1_BASE, X"FFFFFFFF", 256, 16#0001#, "./data/data0.txt", IbCmd);
-- 
--    REPORT LF & LF & LF & "2.Throughput user initialization START" SEVERITY NOTE;
-- 
--    -- read number of cycles (have to be 0 at beginning!)
--    -- SendLocalRead(LB_EP_BASE_ADDR+24,    X"FFFFFFFF", 8, 16#0002#, IbCmd);
-- 
--    -- init number of requests
--    SendLocalWrite(LB_EP_BASE_ADDR+24, X"FFFFFFFF", 8, 16#FFEE#, X"0000000000000005", IbCmd);
-- 
--    -- start whole G2L Bus Master operation -> invoke more BM transfers depending on req_reg
--    start_bm(LB_EP_BASE_ADDR, MEMORY_BASE_ADDR, DOWNSTREAM1_BASE, 4096, X"0002", "01");
-- 
--    -- start whole L2G Bus Master operation -> invoke more BM transfers depending on req_reg
--    -- start_bm(LB_EP_BASE_ADDR, MEMORY_BASE_ADDR, DOWNSTREAM1_BASE, 8, X"0002", "01");
-- 
--    REPORT LF & LF & LF & "2.Throughput user initialization END" SEVERITY NOTE;
-- 
--    -- wait for all dma transfers
--    wait for 10000 ns;
-- 
--    REPORT LF & LF & LF & "2.Number of test cycles: - START" SEVERITY NOTE;
-- 
--    wait until (IB_CLK'event and IB_CLK='1');
-- 
--    -- read number of cycles (have to be more than 0!)
--    SendLocalRead(LB_EP_BASE_ADDR+24,    X"FFFFFFFF", 8, 16#0006#, IbCmd); 
-- 
--    -- wait for read answer
--    wait for 1000 ns;
-- 
--    REPORT LF & LF & LF & "2.Number of test cycles: - END" SEVERITY NOTE;
-- 
--    -- *******************************************************************
--    -- ************************* next test *******************************
--    -- *******************************************************************
-- 
--    -- Init FPGA memory
--    SendLocalWriteFile(DOWNSTREAM1_BASE, X"FFFFFFFF", 256, 16#0001#, "./data/data0.txt", IbCmd);
-- 
--    REPORT LF & LF & LF & "3.Throughput user initialization START" SEVERITY NOTE;
-- 
--    -- read number of cycles (have to be 0 at beginning!)
--    -- SendLocalRead(LB_EP_BASE_ADDR+24,    X"FFFFFFFF", 8, 16#0002#, IbCmd);
-- 
--    -- init number of requests
--    SendLocalWrite(LB_EP_BASE_ADDR+24, X"FFFFFFFF", 8, 16#FFEE#, X"0000000000000005", IbCmd);
-- 
--    -- start whole G2L Bus Master operation -> invoke more BM transfers depending on req_reg
--    -- start_bm(LB_EP_BASE_ADDR, MEMORY_BASE_ADDR, DOWNSTREAM1_BASE, 256, X"0003", "00");
-- 
--    -- start whole L2G Bus Master operation -> invoke more BM transfers depending on req_reg
--    start_bm(LB_EP_BASE_ADDR, MEMORY_BASE_ADDR, DOWNSTREAM1_BASE, 4096, X"0001", "01");
-- 
--    REPORT LF & LF & LF & "3.Throughput user initialization END" SEVERITY NOTE;
-- 
--    -- wait for all dma transfers
--    wait for 10000 ns;
-- 
--    REPORT LF & LF & LF & "3.Number of test cycles: - START" SEVERITY NOTE;
-- 
--    wait until (IB_CLK'event and IB_CLK='1');
-- 
--    -- read number of cycles (have to be more than 0!)
--    SendLocalRead(LB_EP_BASE_ADDR+24,    X"FFFFFFFF", 8, 16#0006#, IbCmd); 
-- 
--    -- wait for read answer
--    wait for 1000 ns;
-- 
--    REPORT LF & LF & LF & "3.Number of test cycles: - END" SEVERITY NOTE;
-- 
--    -- *******************************************************************
--    -- ************************* next test *******************************
--    -- *******************************************************************
-- 
--    -- Init FPGA memory
--    SendLocalWriteFile(DOWNSTREAM1_BASE, X"FFFFFFFF", 256, 16#0001#, "./data/data0.txt", IbCmd);
-- 
--    REPORT LF & LF & LF & "4.Throughput user initialization START" SEVERITY NOTE;
-- 
--    -- read number of cycles (have to be 0 at beginning!)
--    -- SendLocalRead(LB_EP_BASE_ADDR+24,    X"FFFFFFFF", 8, 16#0002#, IbCmd);
-- 
--    -- init number of requests
--    SendLocalWrite(LB_EP_BASE_ADDR+24, X"FFFFFFFF", 8, 16#FFEE#, X"0000000000000005", IbCmd);
-- 
--    -- start whole G2L Bus Master operation -> invoke more BM transfers depending on req_reg
--    start_bm(LB_EP_BASE_ADDR, MEMORY_BASE_ADDR, DOWNSTREAM1_BASE, 4096, X"0002", "01");
-- 
--    -- start whole L2G Bus Master operation -> invoke more BM transfers depending on req_reg
--    -- start_bm(LB_EP_BASE_ADDR, MEMORY_BASE_ADDR, DOWNSTREAM1_BASE, 8, X"0002", "01");
-- 
--    REPORT LF & LF & LF & "4.Throughput user initialization END" SEVERITY NOTE;
-- 
--    -- wait for all dma transfers
--    wait for 10000 ns;
-- 
--    REPORT LF & LF & LF & "4.Number of test cycles: - START" SEVERITY NOTE;
-- 
--    wait until (IB_CLK'event and IB_CLK='1');
-- 
--    -- read number of cycles (have to be more than 0!)
--    SendLocalRead(LB_EP_BASE_ADDR+24,    X"FFFFFFFF", 8, 16#0006#, IbCmd); 
-- 
--    -- wait for read answer
--    wait for 1000 ns;
-- 
--    REPORT LF & LF & LF & "4.Number of test cycles: - END" SEVERITY NOTE;
-- 

   end if;


  wait;
end process;

end architecture TESTBENCH_ARCH; 
