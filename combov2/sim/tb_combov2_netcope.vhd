-- tb_combov2_netcope.vhd: Testbench of COMBOV2 NetCOPE layer card
-- Copyright (C) 2008 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

use work.addr_space.all;
use work.ib_pkg.all; -- Internal Bus Package
use work.ib_bfm_pkg.all; -- Internal Bus Simulation Package 

use work.combov2_user_const.all;
-- DESC_MAN INIT_PHASE_OFFSET
use work.desc_man_pkg.all;
-- DESC_MAN base address
use work.dma_mod_2x64b_rxtx_const.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;
-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   -- UUT test types
   type t_tests is (BASE);

   constant MEMORY_BASE_ADDR  : std_logic_vector(63 downto 0) := X"0000000000000000";
   constant MEMORY_SIZE       : integer := 16#94000#;

   constant TEST           : String := DMA_TYPE;
   
   constant NIC_DATA_DIR   : string := "../../data/";
   constant PACKET_DIR     : string := "../../data/packets/common/";
   constant DESC_DIR       : string := "desc_data";
   constant IFC_COUNT      : integer := 4;
   constant NUM_PACKETS    : integer := 4;
   constant PACKET_SPACE   : time := 1 us;

   -- Clock frequencies
   constant CLK_FREQ          : integer := 125;
   constant XGMII_REFCLK_FREQ : integer := 125;
   
   constant RESET_TIME           : time := 1 us;
   constant INIT_TIME            : time := 15 us;
   constant XGMII_TX_REFCLK_PER  : time := 6.4 ns;
   
   -- DESC_MAN init phase local (IB) address
   constant DESC_INIT_ADDR : std_logic_vector(31 downto 0) :=
               RXTX_DESC_BASE_ADDR + DESC_MAN_INIT_PHASE_OFFSET;

   constant PAC_LB_ADDR : std_logic_vector(31 downto 0) := X"00000800";
   constant PAC_DDM_ADDR : std_logic_vector(31 downto 0) := X"02200000";
   constant PAC_DDM_INIT_ADDR : std_logic_vector(31 downto 0) := X"0227F000";
   -- COMBOV2 NetCOPE signals -------------------------------------------------
   -- ----------------------------------------------------------------------
   -- CLOCKs and RESET
   -- ----------------------------------------------------------------------
   -- CLK:
   signal combov2_clk               : std_logic;
   signal bridge_clk                : std_logic;
   -- reset
   signal bridge_reset              : std_logic;
   signal combov2_reset             : std_logic;

   signal reset_async               : std_logic;
      
   -- ----------------------------------------------------------------------
   -- Interconnection system
   -- ----------------------------------------------------------------------
   signal combov2_internal_bus_down_data        : std_logic_vector(63 downto 0);
   signal combov2_internal_bus_down_sop_n       : std_logic;
   signal combov2_internal_bus_down_eop_n       : std_logic;
   signal combov2_internal_bus_down_src_rdy_n   : std_logic;
   signal combov2_internal_bus_down_dst_rdy_n   : std_logic;
   signal combov2_internal_bus_up_data          : std_logic_vector(63 downto 0);
   signal combov2_internal_bus_up_sop_n         : std_logic;
   signal combov2_internal_bus_up_eop_n         : std_logic;
   signal combov2_internal_bus_up_src_rdy_n     : std_logic;
   signal combov2_internal_bus_up_dst_rdy_n     : std_logic;

   -- IB SIM
   signal internal_bus        : t_internal_bus64;

   -- -------------------------------------------------------------------------
   alias reset       : std_logic is combov2_reset;
   alias clk         : std_logic is combov2_clk;
   signal gnd        : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   gnd <= '0';
   
   -- -------------------------------------------------------------------------
   --                           COMBOV2 INSTANTIATION
   -- -------------------------------------------------------------------------
   COMBOV2_UUT : entity work.COMBOV2_NETCOPE
      port map (
         -- ----------------------------------------------------------------------
         -- CLOCKs and RESET
         -- ----------------------------------------------------------------------
         -- CLK:
         USER_CLK          => bridge_clk,
         -- reset
         RESET             => bridge_reset,

         -- ----------------------------------------------------------------------
         -- XGMII interface from IFC1 (2 ports)
         -- ----------------------------------------------------------------------
         -- RX
         XGMII_RESET    => (others => '0'),
         XGMII_RXCLK    => (others => '0'),
         XGMII_RXD      => (others => '0'),
         XGMII_RXC      => (others => '0'),
         -- TX
         XGMII_TXCLK    => (others => '0'),
         XGMII_TXD      => open,
         XGMII_TXC      => open,
         
         -- ----------------------------------------------------------------------
         -- Interconnection system
         -- ----------------------------------------------------------------------
         IB_CLK            => combov2_clk,
         IB_RST            => combov2_reset,

         IB_DOWN_data      => internal_bus.down.data,
         IB_DOWN_sop_n     => internal_bus.down.sop_n,
         IB_DOWN_eop_n     => internal_bus.down.eop_n,
         IB_DOWN_src_rdy_n => internal_bus.down.src_rdy_n,
         IB_DOWN_dst_rdy_n => internal_bus.down.dst_rdy_n,
         IB_UP_data        => internal_bus.up.data,
         IB_UP_sop_n       => internal_bus.up.sop_n,
         IB_UP_eop_n       => internal_bus.up.eop_n,
         IB_UP_src_rdy_n   => internal_bus.up.src_rdy_n,
         IB_UP_dst_rdy_n   => internal_bus.up.dst_rdy_n,

         INTERRUPT => open,
         INTR_DATA => open,
         INTR_RDY => '1',

         -- ----------------------------------------------------------------------
         -- QDRII Memories
         -- ----------------------------------------------------------------------
   
         -- QDRII Memory 1
            -- Data --
         S0Q            => (others => '0'),
         S0D            => open,
            -- Address --
         S0A            => open,
            -- Control --
         S0BWS_N        => open,
         S0CQ_P         => '0',
         S0CQ_N         => '0',
         S0K_P          => open,
         S0K_N          => open,
         S0C_P          => open,
         S0C_N          => open,
         S0WPS_N        => open,
         S0RPS_N        => open,
         S0DOFF_N       => open,
   
         -- QDRII Memory 2
            -- Data --
         S1Q            => (others => '0'),
         S1D            => open,
            -- Address --
         S1A            => open,
            -- Control --
         S1BWS_N        => open,
         S1CQ_P         => '0',
         S1CQ_N         => '0',
         S1K_P          => open,
         S1K_N          => open,
         S1C_P          => open,
         S1C_N          => open,
         S1WPS_N        => open,
         S1RPS_N        => open,
         S1DOFF_N       => open,

      MCLK1_P        => '1',
      MCLK1_N        => '1',
      MCLK0_P        => '1',
      MCLK0_N        => '1',
      -- PCI Clk 
      GCLK100_P      => '1',
      GCLK100_N      => '1',
      GCLK250_P      => '1',
      GCLK250_N      => '1',
      -- PLL Clk
      XCLK0_P        => '1',
      XCLK0_N        => '1',
      XCLK1_P        => '1',
      XCLK1_N        => '1',
      XCLK2          => '1',
      FQTXD          => open,
      FQRXD          => '1',
      FQLED          => open,

      PPS_N          => clk,
      PTM_CLK        => '1'
      );

   -- -------------------------------------------------------------------------
   --                           CLOCKs & RESETs
   -- -------------------------------------------------------------------------
   -- BUS RESET generator
   busresetp : process
   begin
      bridge_reset <= '1', '0' after RESET_TIME;
      wait;
   end process;

   -- CORE_CLK clock generator
   clk_genp: process
      variable halfcycle   : time := 1 us/(2*CLK_FREQ);
   begin
      bridge_clk  <= '1';
      wait for halfcycle;
      bridge_clk  <= '0';
      wait for halfcycle;
   end process;

   -- -------------------------------------------------------------------------
   --                         INTERNAL BUS SIMULATION
   -- -------------------------------------------------------------------------
   IB_BFM_I : entity work.IB_BFM
      generic map(
          MEMORY_BASE_ADDR    => MEMORY_BASE_ADDR,
          MEMORY_SIZE         => MEMORY_SIZE
      )
      port map(
         -- Common interface
         CLK               => clk,
         -- Internal Bus Interface
         IB                => internal_bus
      );

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb : process
   -------------------------------------------------------------------
   -- Variables and constants declarations
   -------------------------------------------------------------------
   -- size of packet for TX DMA controller
   constant TX_PACKET_SIZE : integer := 16#48#;
   -- TX packets per memory page
   constant TX_PACKETS_PER_MEMPAGE  : integer := 56;
   -- size of a page boundary packet for TX DMA controller
   constant TX_BOUNDARY_PACKET_SIZE : integer := 16#40#;
   
   -- number of packets for TX DMA controller
   -- constant TX_PACKET_NUM  : integer := 58;
   constant TX_PACKET_NUM  : integer := 110;
   -- current value of SwEndPtr for TX DMA controller
   variable tx_current_sw_end_ptr : integer := 0;
-- ----------------------------------------------------------------------------
--                    Procedures declaration
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

-- Start busmaster operation
procedure pac_start_rx(channel : in integer) is
   variable ib_channel_addr : std_logic_vector(31 downto 0) := PAC_DDM_ADDR + channel*16#1000#;
   variable lb_channel_addr : std_logic_vector(31 downto 0) := PAC_LB_ADDR + channel*16#40#;
   variable init_channel_addr : std_logic_vector(31 downto 0) := PAC_DDM_INIT_ADDR + channel*16#8#;

begin

   -- set initial descriptor
   SendLocalWrite(init_channel_addr + 16#00# , X"08000000", 4, 16#1234#, X"00000000" & X"00000000", IbCmd);
   SendLocalWrite(init_channel_addr + 16#04# , X"08000000", 4, 16#1234#, X"00000000" & X"00000000", IbCmd);

   -- move tail pointer
   SendLocalWrite(lb_channel_addr + 16#0C# , X"08000000", 4, 16#1234#, X"00000000" & X"00001000", IbCmd);

   -- clear rx sw cnt
   SendLocalWrite(lb_channel_addr + 16#14# , X"08000000", 4, 16#1234#, X"00000000" & X"00000000", IbCmd);
   -- clear rx hw cnt
   SendLocalRead(lb_channel_addr + 16#08#, X"ffffffff", 4, 222, IbCmd);

   -- enable IBUFs 
   SendLocalWrite(conv_std_logic_vector(16#1020#+ channel*16#100#, 32) , X"ffffffff", 4, 1, X"0000000000000001", IbCmd);

   -- set timeout
   SendLocalWrite(lb_channel_addr + 16#10# , X"08000000", 4, 16#1234#, X"00000000" & X"00000800", IbCmd);

   -- start
   SendLocalWrite(lb_channel_addr + 16#00# , X"08000000", 4, 16#1234#, X"00000000" & X"00000002", IbCmd);

   SendLocalRead(lb_channel_addr + 16#04#, X"ffffffff", 4, 222, IbCmd);
end pac_start_rx;

procedure pac_start_tx(channel : in integer) is
   variable ib_channel_addr : std_logic_vector(31 downto 0) := PAC_DDM_ADDR + channel*16#1000#;
   variable lb_channel_addr : std_logic_vector(31 downto 0) := PAC_LB_ADDR + channel*16#40#;
   variable init_channel_addr : std_logic_vector(31 downto 0) := PAC_DDM_INIT_ADDR + channel*16#8#;

begin

   -- set initial descriptor
   SendLocalWrite(init_channel_addr + 16#00# , X"08000000", 4, 16#1234#, X"00000000" & X"00001000", IbCmd);
   SendLocalWrite(init_channel_addr + 16#04# , X"08000000", 4, 16#1234#, X"00000000" & X"00000000", IbCmd);

   -- move tail pointer
   SendLocalWrite(lb_channel_addr + 16#0C# , X"08000000", 4, 16#1234#, X"00000000" & X"00000000", IbCmd);

   -- clear rx sw cnt
   SendLocalWrite(lb_channel_addr + 16#14# , X"08000000", 4, 16#1234#, X"00000000" & X"00000000", IbCmd);
   -- clear rx hw cnt
   SendLocalRead(lb_channel_addr + 16#08#, X"ffffffff", 4, 222, IbCmd);

   -- enable 0BUFs 
   SendLocalWrite(conv_std_logic_vector(16#2020#+ channel*16#100#, 32) , X"ffffffff", 4, 1, X"0000000000000001", IbCmd);

   -- set timeout
   SendLocalWrite(lb_channel_addr + 16#10# , X"08000000", 4, 16#1234#, X"00000000" & X"00000800", IbCmd);

   -- start
   SendLocalWrite(lb_channel_addr + 16#00# , X"08000000", 4, 16#1234#, X"00000000" & X"00000002", IbCmd);

   SendLocalRead(lb_channel_addr + 16#04#, X"ffffffff", 4, 222, IbCmd);
end pac_start_tx;

procedure pac_stop_channel(channel : in integer) is
   variable lb_channel_addr : std_logic_vector(31 downto 0) := PAC_LB_ADDR + channel*16#40#;
begin
   SendLocalWrite(lb_channel_addr, X"08000000", 4, 16#1234#, X"00000000" & X"00000000", IbCmd);
end pac_stop_channel;


-- ----------------------------------------------------------------------------
--                        Testbench Body
-- ----------------------------------------------------------------------------
begin

   wait for INIT_TIME;

   -- -------------- All component test ---------------------------------------
   if (TEST = "SZE") then

      -- Host memory address space regions
      -- +----------------+ 0x94000
      -- |    TX1_DESC    |
      -- +----------------+ 0x93000
      -- |    RX1_DESC    |
      -- +----------------+ 0x92000
      -- |                |
      -- |                |
      -- |                |
      -- |   DEADBEEF     |
      -- |      sector    |
      -- |                |
      -- |                |
      -- +----------------+ 0x72000
      -- |     TX1        |
      -- |     ring       |
      -- |    buffer      |
      -- +----------------+ 0x62000
      -- |     TX0        |
      -- |     ring       |
      -- |    buffer      |
      -- +----------------+ 0x52000
      -- |                |
      -- |                |
      -- |                |
      -- |   DEADBEEF     |
      -- |      sector    |
      -- |                |
      -- |                |
      -- +----------------+ 0x32000
      -- |     RX1        |
      -- |     ring       |
      -- |    buffer      |
      -- +----------------+ 0x22000
      -- |     RX0        |
      -- |     ring       |
      -- |    buffer      |
      -- +----------------+ 0x12000
      -- |    TX0_DESC    |
      -- +----------------+ 0x11000
      -- |    RX0_DESC    |
      -- +----------------+ 0x10000
      -- |                |
      -- |   DEADBEEF     |
      -- |      sector    |
      -- |                |
      -- +----------------+ 0x00000

      -- Set IB logging
      setFileLogging(true, IbCmd);

      -- Initialize dead sector
      for i in 0 to 15 loop
         InitMemoryFromAddr(16#1000#, i*16#1000#,  DESC_DIR & "/dead_beef_sector.txt", IbCmd);
      end loop;
      
      -- Initialize RX0/TX0 descriptors (BUG in IB_BFM InitHostMemory)
      InitMemoryFromAddr(16#1000#, 16#10000#, DESC_DIR & "/rx0_desc_data.txt", IbCmd);
      InitMemoryFromAddr(16#1000#, 16#11000#, DESC_DIR & "/tx0_desc_data.txt", IbCmd);

      -- Zero out RX MEMs
      for i in 0 to 16*4-1 loop
         InitMemoryFromAddr(16#1000#, i*16#1000# + 16#12000#, DESC_DIR & "/dead_beef_sector.txt", IbCmd);
      end loop;

      -- Initialize TX MEM
      for flow in 0 to 2-1 loop
         for i in 0 to 9 loop
            InitMemoryFromAddr(16#1000#, 16#52000# + flow*16#10000# + i*16#1000#,
               "dumps/00" & character'val(i+16#30#) & "_dump.dump", IbCmd);
         end loop;
         for i in 10 to 15 loop
            InitMemoryFromAddr(16#1000#, 16#52000# + flow*16#10000# + i*16#1000#,
               "dumps/01" & character'val(i-10+16#30#) & "_dump.dump", IbCmd);
         end loop;
      end loop;

      -- Zero out unused TX part
      for flow in 2 to 4-1 loop
         for i in 0 to 15 loop
            InitMemoryFromAddr(16#1000#, 16#52000# + flow*16#10000# + i*16#1000#,
               DESC_DIR & "/dead_beef_sector.txt", IbCmd);
         end loop;
      end loop;

      -- Initialize RX/TX descriptors list (for IFC 1, 2, 3)
      InitMemoryFromAddr(16#1000#, 16#92000#, DESC_DIR & "/rx1_desc_data.txt", IbCmd);
      InitMemoryFromAddr(16#1000#, 16#93000#, DESC_DIR & "/tx1_desc_data.txt", IbCmd);


      -- Debug out the initialized host memory
      -- ShowMemory(IbCmd);

      wait for 1 us;


      -------------------------------------------------------------------
      -- Initialize descriptor manager
      -------------------------------------------------------------------
      -- Note: DESC_INIT_ADDR is defined in desc_man_pkg.vhd

      -- write address of first desc for channel 0 -- RX0
      SendLocalWrite(DESC_INIT_ADDR + 16#00# , X"08000000", 4, 16#1234#, X"00000000" & X"00010000", IbCmd);
      SendLocalWrite(DESC_INIT_ADDR + 16#04# , X"08000000", 4, 16#1234#, X"00000000" & X"00000000", IbCmd);

      -- write address of first desc for channel 1 -- TX0
      SendLocalWrite(DESC_INIT_ADDR + 16#08# , X"08000000", 4, 16#1234#, X"00000000" & X"00011000", IbCmd);
      SendLocalWrite(DESC_INIT_ADDR + 16#0C# , X"08000000", 4, 16#1234#, X"00000000" & X"00000000", IbCmd);

      -- write address of first desc for channel 2 -- RX1
      SendLocalWrite(DESC_INIT_ADDR + 16#10# , X"08000000", 4, 16#1234#, X"00000000" & X"00092000", IbCmd);
      SendLocalWrite(DESC_INIT_ADDR + 16#14# , X"08000000", 4, 16#1234#, X"00000000" & X"00000000", IbCmd);

      -- write address of first desc for channel 3 -- TX1
      SendLocalWrite(DESC_INIT_ADDR + 16#18# , X"08000000", 4, 16#1234#, X"00000000" & X"00093000", IbCmd);
      SendLocalWrite(DESC_INIT_ADDR + 16#1C# , X"08000000", 4, 16#1234#, X"00000000" & X"00000000", IbCmd);

      -------------------------------------------------------------------
      -- Initialize RX and TX DMA_CTRLs
      -------------------------------------------------------------------
      -- RX0 init ----------------------------------------------------------------
      -- initialization - Write sw buffer mask == sw buffer size
      SendLocalWrite(X"00000810", X"08000000", 4, 16#1234#, X"00000000" & X"0000FFFF", IbCmd);
      -- initialization - Write start command to controlRegiter 
      SendLocalWrite(X"00000800", X"08000000", 4, 16#1234#, X"00000000" & X"00000001", IbCmd);

      -- TX0 init ----------------------------------------------------------------
      -- initialization - Write sw buffer mask == sw buffer size
      SendLocalWrite(X"00000850", X"08000000", 4, 16#1234#, X"00000000" & X"0000FFFF", IbCmd);
      -- initialization - Write start command to controlRegiter 
      SendLocalWrite(X"00000840", X"08000000", 4, 16#1234#, X"00000000" & X"00000001", IbCmd);

      -- RX1 init ----------------------------------------------------------------
      -- initialization - Write sw buffer mask == sw buffer size
      SendLocalWrite(X"00000890", X"08000000", 4, 16#1234#, X"00000000" & X"0000FFFF", IbCmd);
      -- initialization - Write start command to controlRegiter 
      SendLocalWrite(X"00000880", X"08000000", 4, 16#1234#, X"00000000" & X"00000001", IbCmd);

      -- TX1 init ----------------------------------------------------------------
      -- initialization - Write sw buffer mask == sw buffer size
      SendLocalWrite(X"000008D0", X"08000000", 4, 16#1234#, X"00000000" & X"0000FFFF", IbCmd);
      -- initialization - Write start command to controlRegiter 
      SendLocalWrite(X"000008C0", X"08000000", 4, 16#1234#, X"00000000" & X"00000001", IbCmd);

      -- Interrupt status registers -------------------------------------------
      SendLocalRead(X"02280000", X"ffffffff", 8, 222, IbCmd);  -- RX Status register
      SendLocalRead(X"02280008", X"ffffffff", 8, 222, IbCmd);  -- TX Status register

      wait for 10 us;

      -- IBUFs enable
      SendLocalWrite(X"00001020", X"ffffffff", 4, 1, X"0000000000000001", IbCmd);
      SendLocalWrite(X"00001120", X"ffffffff", 4, 2, X"0000000000000001", IbCmd);

      -- OBUFs enable
      SendLocalWrite(X"00002020", X"ffffffff", 4, 1, X"0000000000000001", IbCmd);
      SendLocalWrite(X"00002120", X"ffffffff", 4, 2, X"0000000000000001", IbCmd);

      -- Test TS_UNIT
      SendLocalWrite(X"00010100", X"ffffffff", 4, 3, X"0000000000000101", IbCmd);
      SendLocalWrite(X"00010108", X"ffffffff", 8, 3, X"FFFFFFFFFFFFFFFF", IbCmd);
      SendLocalRead(X"00010100", X"ffffffff", 4, 3, IbCmd);  -- TX Status register

      -------------------------------------------------------------------
      -- TX transmission test
      -- If you want to transmit at more TX ports, you have to change
      -- pointers manually for other interfaces as well
      -------------------------------------------------------------------
      tx_current_sw_end_ptr := 16#FF78#;
      SendLocalWrite(X"0000084C", X"08000000", 4, 16#1234#, X"00000000" & conv_std_logic_vector(tx_current_sw_end_ptr, 32), IbCmd);
      SendLocalWrite(X"000008CC", X"08000000", 4, 16#1234#, X"00000000" & conv_std_logic_vector(tx_current_sw_end_ptr, 32), IbCmd);

      -------------------------------------------------------------------
      -- Wait for processing and read some data from SW buffer
      -------------------------------------------------------------------
      wait for 40 us;

      SendLocalWrite(X"00000808", X"08000000", 4, 16#1234#, X"00000000" & X"00000100", IbCmd);
      SendLocalWrite(X"00000888", X"08000000", 4, 16#1234#, X"00000000" & X"00000100", IbCmd);
      wait for 20 us;
      SendLocalWrite(X"00000808", X"08000000", 4, 16#1234#, X"00000000" & X"00001800", IbCmd);
      SendLocalWrite(X"00000888", X"08000000", 4, 16#1234#, X"00000000" & X"00001800", IbCmd);
      wait for 120 us;
      SendLocalWrite(X"00000808", X"08000000", 4, 16#1234#, X"00000000" & X"00000100", IbCmd);
      SendLocalWrite(X"00000888", X"08000000", 4, 16#1234#, X"00000000" & X"00000100", IbCmd);
      wait for 50 us;

      -------------------------------------------------------------------
      -- Interrupt status registers read test
      -------------------------------------------------------------------
      SendLocalRead(X"02280000", X"ffffffff", 8, 222, IbCmd);  -- RX Status register
      SendLocalRead(X"02280008", X"ffffffff", 8, 222, IbCmd);  -- TX Status register

   end if;

   if (TEST = "PAC") then
      -- Host memory address space regions
      -- +----------------+ 0x94000
      -- |    TX1_DESC    |
      -- +----------------+ 0x93000
      -- |    RX1_DESC    |
      -- +----------------+ 0x92000
      -- |                |
      -- |                |
      -- |                |
      -- |   DEADBEEF     |
      -- |      sector    |
      -- |                |
      -- |                |
      -- +----------------+ 0x72000
      -- |     TX1        |
      -- |     ring       |
      -- |    buffer      |
      -- +----------------+ 0x62000
      -- |     TX0        |
      -- |     ring       |
      -- |    buffer      |
      -- +----------------+ 0x52000
      -- |                |
      -- |                |
      -- |                |
      -- |   DEADBEEF     |
      -- |      sector    |
      -- |                |
      -- |                |
      -- +----------------+ 0x32000
      -- |     RX1        |
      -- |     ring       |
      -- |    buffer      |
      -- +----------------+ 0x22000
      -- |     RX0        |
      -- |     ring       |
      -- |    buffer      |
      -- +----------------+ 0x12000
      -- |    TX0_DESC    |
      -- +----------------+ 0x11000
      -- |    RX0_DESC    |
      -- +----------------+ 0x10000
      -- |                |
      -- |   DEADBEEF     |
      -- |      sector    |
      -- |                |
      -- +----------------+ 0x00000

      -- Set IB logging
      setFileLogging(true, IbCmd);

--       -- Initialize dead sector
--       for i in 0 to 15 loop
--          InitMemoryFromAddr(16#1000#, i*16#1000#,  DESC_DIR & "/dead_beef_sector.txt", IbCmd);
--       end loop;
      
      -- Initialize RX0/TX0 descriptors (BUG in IB_BFM InitHostMemory)
      InitMemoryFromAddr(16#1000#, 16#0000#, DESC_DIR & "/pac_rx0_desc_data.txt", IbCmd);
      InitMemoryFromAddr(16#1000#, 16#1000#, DESC_DIR & "/pac_tx0_desc_data.txt", IbCmd);

      -- Zero out RX MEMs
      for i in 0 to 16*4-1 loop
         InitMemoryFromAddr(16#1000#, i*16#1000# + 16#2000#, DESC_DIR & "/dead_beef_sector.txt", IbCmd);
      end loop;

--       -- Initialize TX MEM
--       for flow in 0 to 2-1 loop
--          for i in 0 to 9 loop
--             InitMemoryFromAddr(16#1000#, 16#52000# + flow*16#10000# + i*16#1000#,
--                "dumps/00" & character'val(i+16#30#) & "_dump.dump", IbCmd);
--          end loop;
--          for i in 10 to 15 loop
--             InitMemoryFromAddr(16#1000#, 16#52000# + flow*16#10000# + i*16#1000#,
--                "dumps/01" & character'val(i-10+16#30#) & "_dump.dump", IbCmd);
--          end loop;
--       end loop;
-- 
--       -- Zero out unused TX part
--       for flow in 2 to 4-1 loop
--          for i in 0 to 15 loop
--             InitMemoryFromAddr(16#1000#, 16#52000# + flow*16#10000# + i*16#1000#,
--                DESC_DIR & "/dead_beef_sector.txt", IbCmd);
--          end loop;
--       end loop;
-- 
--       -- Initialize RX/TX descriptors list (for IFC 1, 2, 3)
--       InitMemoryFromAddr(16#1000#, 16#92000#, DESC_DIR & "/rx1_desc_data.txt", IbCmd);
--       InitMemoryFromAddr(16#1000#, 16#93000#, DESC_DIR & "/tx1_desc_data.txt", IbCmd);


      -- Debug out the initialized host memory
      -- ShowMemory(IbCmd);

      -- time offset 15us
      wait for 1 us;

      -- set Tx global upload address
      SendLocalWrite(PAC_LB_ADDR + 16#58# , X"08000000", 4, 16#1234#, X"00000000" & X"00044000", IbCmd);
      SendLocalWrite(PAC_LB_ADDR + 16#5C# , X"08000000", 4, 16#1234#, X"00000000" & X"00000000", IbCmd);

      for i in 0 to 0 loop
      pac_start_rx(0);
      pac_start_tx(1);
      wait for 1 us;
      pac_start_rx(2);
      pac_start_tx(3);

--       wait for 5 us;
--       -- move tail pointer
--       SendLocalWrite(PAC_LB_ADDR + 16#4C# , X"08000000", 4, 16#1234#, X"00000000" & X"00000004", IbCmd);
--       wait for 1 us;
--       -- set timeout
--       SendLocalWrite(PAC_LB_ADDR + 16#50# , X"08000000", 4, 16#1234#, X"00000000" & X"00000800", IbCmd);

--       wait for 5 us;
--       -- move tail pointer
--       SendLocalWrite(PAC_LB_ADDR + 16#CC# , X"08000000", 4, 16#1234#, X"00000000" & X"00000001", IbCmd);
--       wait for 1 us;
--       -- set timeout
--       SendLocalWrite(PAC_LB_ADDR + 16#D0# , X"08000000", 4, 16#1234#, X"00000000" & X"00000800", IbCmd);



      wait for 250 us;

      pac_stop_channel(0);
      pac_stop_channel(1);
      pac_stop_channel(2);
      pac_stop_channel(3);

      end loop;

--       -- set channel 0 timeout
--       SendLocalWrite(PAC_LB_ADDR + 16#10# , X"08000000", 4, 16#1234#, X"00000000" & X"00000100", IbCmd);
--       wait for 10 us;
--       -- move channel 0 tail pointer
--       SendLocalWrite(PAC_LB_ADDR + 16#0C# , X"08000000", 4, 16#1234#, X"00000000" & X"0000000C", IbCmd);
-- 
--       -------------------------------------------------------------------
--       -- Interrupt status registers read test
--       -------------------------------------------------------------------
--       SendLocalRead(X"02280000", X"ffffffff", 8, 222, IbCmd);  -- RX Status register
--       SendLocalRead(X"02280008", X"ffffffff", 8, 222, IbCmd);  -- TX Status register
-- 

   end if;

   wait;

end process;
-- ----------------------------------------------------------------------------
end architecture behavioral;
