-- dma_ctrl_tb.vhd: DMA control block testbench
-- Copyright (C) 2007 CESNET
-- Author(s): Petr Kastovsky <kastovsky@liberouter.org>
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
--
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use ieee.numeric_std.all;

-- package with LB records
use work.lb_pkg.all;
-- package with IB records
use work.ib_pkg.all;
-- ib_sim package
use work.ib_sim_oper.all;
use work.math_pack.all;
use work.ib_bfm_pkg.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant CLKPER      : time := 10 ns;
   constant IFCS       : integer := 4;
   constant gndvec      : std_logic_vector(128 downto 0) := (others => '0');
   constant IB_EP_LIMIT : std_logic_vector(31 downto 0) := X"00200000";
   constant LB_RT_LIMIT : std_logic_vector(31 downto 0) := X"00001000";
   constant LB_EP_LIMIT : std_logic_vector(31 downto 0) := X"00001000";
   constant LB_RT_BASE_ADDR : std_logic_vector(31 downto 0) := X"00800000";
   constant LB_EP_BASE_ADDR : std_logic_vector(31 downto 0) := X"00800000";

   constant LB_EP_FREQUENCY : integer := 100;
   constant LB_EP_BUFFER_EN : boolean := false;

   signal CLK           : std_logic;
   signal RESET         : std_logic;
   alias  ib_clk        : std_logic is CLK;

   signal internal_bus  : t_internal_bus64;
   signal switch1_port1 : t_internal_bus64;
   signal switch1_port2 : t_internal_bus64;
   signal local_bus16   : t_local_bus16;

   signal ib_wr         : t_ibmi_write64;
   signal ib_rd         : t_ibmi_read64s;
   signal ib_bm         : t_ibbm_64;
   signal mi32          : t_mi32;

   signal rx_newlen     : std_logic_vector(IFCS*16-1 downto 0);
   signal rx_newlen_dv  : std_logic_vector(IFCS-1 downto 0);
   signal rx_newlen_rdy : std_logic_vector(IFCS-1 downto 0);
   signal rx_rellen     : std_logic_vector(IFCS*16-1 downto 0);
   signal rx_rellen_dv  : std_logic_vector(IFCS-1 downto 0);

   signal tx_newlen     : std_logic_vector(IFCS*16-1 downto 0);
   signal tx_newlen_dv  : std_logic_vector(IFCS-1 downto 0);
   signal tx_newlen_rdy : std_logic_vector(IFCS-1 downto 0);
   signal tx_rellen     : std_logic_vector(IFCS*16-1 downto 0);
   signal tx_rellen_dv  : std_logic_vector(IFCS-1 downto 0);

   signal interrupt     : std_logic_vector(2*IFCS-1 downto 0);
begin

-- ------------------------------------------------------------------
-- UUT Instantion
uut : entity work.pac_dma_ctrl
   generic map (
      IFCS              => IFCS
   )
   port map (
      -- Common signals
      CLK      => CLK,
      RESET    => RESET,

      INTERRUPT => interrupt,
      -- Data interface
      -- Write interface
      IB_WR_ADDR     => ib_wr.addr,
      IB_WR_DATA     => ib_wr.data,
      IB_WR_BE       => ib_wr.be,
      IB_WR_REQ      => ib_wr.req,
      IB_WR_RDY      => ib_wr.rdy,

      -- Read interface
      IB_RD_ADDR     => ib_rd.ADDR,
      IB_RD_DATA     => ib_rd.DATA,
      IB_RD_BE       => ib_rd.BE,
      IB_RD_REQ      => ib_rd.REQ,
      IB_RD_ARDY     => ib_rd.ARDY,
      IB_RD_SRC_RDY  => ib_rd.SRC_RDY,

      -- Bus master interface
      IB_BM_GADDR     => ib_bm.global_addr,
      IB_BM_LADDR     => ib_bm.local_addr,
      IB_BM_LENGTH    => ib_bm.length,
      IB_BM_TAG       => ib_bm.tag,
      IB_BM_TTYPE     => ib_bm.trans_type,
      IB_BM_REQ       => ib_bm.req,
      IB_BM_ACK       => ib_bm.ack,
      -- Output
      IB_BM_OP_TAG    => ib_bm.op_tag,
      IB_BM_OP_DONE   => ib_bm.op_done,

      -- SW memory interface
      MI_SW_DWR      => mi32.DWR,
      MI_SW_ADDR     => mi32.ADDR,
      MI_SW_RD       => mi32.RD,
      MI_SW_WR       => mi32.WR,
      MI_SW_BE       => mi32.BE,
      MI_SW_DRD      => mi32.DRD,
      MI_SW_ARDY     => mi32.ARDY,
      MI_SW_DRDY     => mi32.DRDY,

      -- Receive buffer interface
      RX_NEWLEN     => rx_newlen,
      RX_NEWLEN_DV  => rx_newlen_dv,
      RX_NEWLEN_RDY => rx_newlen_rdy,
      RX_RELLEN     => rx_rellen,
      RX_RELLEN_DV  => rx_rellen_dv,

      -- Receive buffer interface
      TX_NEWLEN     => tx_newlen,
      TX_NEWLEN_DV  => tx_newlen_dv,
      TX_NEWLEN_RDY => tx_newlen_rdy,
      TX_RELLEN     => tx_rellen,
      TX_RELLEN_DV  => tx_rellen_dv
   );

-- Internal Bus Bus Functional Model ------------------------------------------
IB_BFM_U : entity work.IB_BFM
   generic map (
       MEMORY_SIZE => 1024,
       MEMORY_BASE_ADDR => X"0000DEAD" & X"00000000"
   )
   port map (
      CLK          => ib_clk,
      -- Internal Bus Interface
      IB           => internal_bus
   );

-- Internal Bus Switch -----------------------------------------------------
IB_SWITCH1_I : entity work.IB_SWITCH
   generic map (
      -- Data Width (64/128)
      DATA_WIDTH        => 64,
      -- Port 0 Address Space
      SWITCH_BASE        => X"00000000",
      SWITCH_LIMIT       => X"01000000",
      -- Port 1 Address Space
      DOWNSTREAM0_BASE   => X"00000000",
      DOWNSTREAM0_LIMIT  => X"00400000",
      -- Port 2 Address Space
      DOWNSTREAM1_BASE   => X"00800000",
      DOWNSTREAM1_LIMIT  => X"00001000"
   )

   port map (
      -- Common Interface
      IB_CLK         => ib_clk,
      IB_RESET       => RESET,
      -- Upstream Port
      PORT0          => internal_bus,
      -- Downstream Ports
      PORT1          => switch1_port1,
      PORT2          => switch1_port2
   );
   
-- Internal Bus Endpoint ---------------------------------------------------
IB_ENDPOINT_I : entity work.IB_ENDPOINT_MASTER
   generic map(
      LIMIT         => IB_EP_LIMIT
   )
   port map(
      -- Common Interface
      IB_CLK        => ib_clk,
      IB_RESET      => RESET,
      -- Internal Bus Interface
      INTERNAL_BUS  => switch1_port1,
      -- User Component Interface
      WR            => ib_wr,
      RD            => ib_rd,

      -- Busmaster
      BM            => ib_bm
   );

-- -----------------------Portmaping of LB root -------------------------------
LB_ROOT_U : entity work.LB_ROOT
   generic map (
      BASE_ADDR      => LB_RT_BASE_ADDR,
      LIMIT          => LB_RT_LIMIT
   )
   port map (
      -- Common Interface
      IB_CLK         => ib_clk,
      RESET          => RESET,

      -- Local Bus Interface
      INTERNAL_BUS   => switch1_port2,

      -- Local Bus Interface
      LOCAL_BUS      => local_bus16
  );

-- -----------------------Portmaping of LB_Endpoint ---------------------------   
LB_ENDPOINT_U : entity work.LB_ENDPOINT
   generic map (
      BASE_ADDR      => LB_EP_BASE_ADDR,
      LIMIT          => LB_EP_LIMIT,
      FREQUENCY      => LB_EP_FREQUENCY,
      BUFFER_EN      => LB_EP_BUFFER_EN
   )
   port map (
      -- Common Interface
      RESET          => RESET,

      -- Local Bus Interface
      LB_CLK         => ib_clk,
      LOCALBUS       => local_bus16,

      -- User Component Interface
      CLK            => CLK,
      MI32           => mi32
  );

-- clk clock generator
clkgen_CLK: process
begin
   CLK <= '1';
   wait for CLKPER/2;
   CLK <= '0';
   wait for CLKPER/2;
end process;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb : process
-- ----------------------------------------------------------------
--                    Procedures declaration
-- ----------------------------------------------------------------
-- ----------------------------------------------------------------


begin
   InitMemory(256, "desc_data.txt", IbCmd);


   RESET <= '1', '0' after 100 ns;
   wait for 1 us;
   -- ib access - descriptor initialization
   -- set init descriptor for channel 0
--    SendLocalWrite(DDM_IB_BASE + 16#7F000#, X"00000000", 8, 16#0000#, X"0000DEAD" & X"00000000", IbCmd);
--    -- set init descriptor for channel 1
--    SendLocalWrite(DDM_IB_BASE + 16#7F008#, X"00000000", 8, 16#ABCD#, X"0000DEAD" & X"00000000", IbCmd);
--    -- set init descriptor for channel 2
--    SendLocalWrite(DDM_IB_BASE + 16#7F010#, X"00000000", 8, 16#ABCD#, X"0000DEAD" & X"00000000", IbCmd);
--    -- set init descriptor for channel 3
--    SendLocalWrite(DDM_IB_BASE + 16#7F018#, X"00000000", 8, 16#ABCD#, X"0000DEAD" & X"00000060", IbCmd);


   -- register access
   -- start channel 0
--    SendLocalWrite(DDM_MI_BASE + 16#000#, X"00000000", 4, 16#ABCD#, X"00000000" & X"00000002", IbCmd);
--    -- start channel 1
--    SendLocalWrite(DDM_MI_BASE + 16#020#, X"00000000", 4, 16#ABCD#, X"00000000" & X"00000002", IbCmd);
--    -- start channel 2
--    SendLocalWrite(DDM_MI_BASE + 16#040#, X"00000000", 4, 16#ABCD#, X"00000000" & X"00000002", IbCmd);
--    -- start channel 3
--    SendLocalWrite(DDM_MI_BASE + 16#060#, X"00000000", 4, 16#ABCD#, X"00000000" & X"00000002", IbCmd);


--    -- move channel 0 tail pointer
--    SendLocalWrite(DDM_MI_BASE + 16#00C#, X"00000000", 4, 16#ABCD#, X"00000000" & X"00000002", IbCmd);
-- 
--    wait for 100*CLKPER;
--    -- move channel 1 tail pointer
--    SendLocalWrite(DDM_MI_BASE + 16#02C#, X"00000000", 4, 16#ABCD#, X"00000000" & X"00000003", IbCmd);
-- 
--    wait for 100*CLKPER;
--    -- move channel 2 tail pointer
--    SendLocalWrite(DDM_MI_BASE + 16#04C#, X"00000000", 4, 16#ABCD#, X"00000000" & X"00000005", IbCmd);
-- 
--    wait for 100*CLKPER;
--    -- move channel 0 tail pointer
--    SendLocalWrite(DDM_MI_BASE + 16#00C#, X"00000000", 4, 16#ABCD#, X"00000000" & X"00000006", IbCmd);

--    SendLocalRead(DDM_MI_BASE + 16#000#, X"DEADBEEF", 4, 123, IbCmd);
--    SendLocalRead(DDM_MI_BASE + 16#020#, X"DEADBEEF", 4, 123, IbCmd);
--    SendLocalRead(DDM_MI_BASE + 16#040#, X"DEADBEEF", 4, 123, IbCmd);

--    SendLocalRead(DDM_MI_BASE + 16#004#, X"DEADBEEF", 4, 123, IbCmd);
--    SendLocalRead(DDM_MI_BASE + 16#008#, X"DEADBEEF", 4, 123, IbCmd);
--    SendLocalRead(DDM_MI_BASE + 16#00C#, X"DEADBEEF", 4, 123, IbCmd);

   wait;
end process;


end architecture behavioral;
