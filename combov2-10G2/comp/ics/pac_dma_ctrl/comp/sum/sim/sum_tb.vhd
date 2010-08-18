-- sum_tb.vhd: Status update manager testbench
-- Copyright (C) 2009 CESNET
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
use work.pac_dma_pkg.all;
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
   constant SUM_IB_BASE    : std_logic_vector := X"00000000";
   constant SUM_MI_BASE    : std_logic_vector := X"00800000";
   constant DMA_DATA_WIDTH : integer := 32;
   constant IFCS       : integer := 8;
   constant BLOCK_SIZE  : integer := 4;
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

   signal interrupt     : std_logic_vector(2*IFCS-1 downto 0);
   signal idle          : std_logic_vector(2*IFCS-1 downto 0);
   signal flush         : std_logic_vector(2*IFCS-1 downto 0);
   signal init          : std_logic_vector(2*IFCS-1 downto 0);

   signal dma_addr      : std_logic_vector(log2(128/DMA_DATA_WIDTH)-1 downto 0);
   signal dma_dout      : std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
   signal dma_req       : std_logic;
   signal dma_ack       : std_logic;
   signal dma_done      : std_logic;
   signal dma_tag       : std_logic_vector(15 downto 0);

   -- RxReqFifo interface
   signal rx_rf_raddr   : std_logic_vector(abs(log2(IFCS)-1) downto 0);
   signal rx_rf_dout    : std_logic_vector(log2(BLOCK_SIZE) + 64 downto 0);
   signal rx_rf_dvld    : std_logic;
   signal rx_rf_empty   : std_logic_vector(IFCS-1 downto 0);
   signal rx_rf_read    : std_logic;
   signal rx_rf_status  : std_logic_vector(log2(BLOCK_SIZE+1)*IFCS-1 downto 0);

   -- Rx status update
   signal rx_su_addr    : std_logic_vector(abs(log2(IFCS)-1) downto 0);
   signal rx_su_data    : std_logic_vector(NUM_FLAGS+16-1 downto 0);
   signal rx_su_dvld    : std_logic;
   signal rx_su_hfull   : std_logic_vector(IFCS-1 downto 0);

   -- Tx status update
   signal tx_su_addr    : std_logic_vector(abs(log2(IFCS)-1) downto 0);
   signal tx_su_data    : std_logic_vector(NUM_FLAGS-1 downto 0);
   signal tx_su_dvld    : std_logic;
   signal tx_su_hfull   : std_logic_vector(IFCS-1 downto 0);

   signal mozes         : std_logic;

   signal internal_bus  : t_internal_bus64;
   signal switch1_port1 : t_internal_bus64;
   signal switch1_port2 : t_internal_bus64;
   signal local_bus16   : t_local_bus16;

   signal ib_wr         : t_ibmi_write64;
   signal ib_rd         : t_ibmi_read64s;
   signal ib_bm         : t_ibbm_64;
   signal mi32          : t_mi32;
   signal reg_rx_rf_read : std_logic;
   signal reg_rx_rf_read_we : std_logic;

begin

-- ------------------------------------------------------------------
-- UUT Instantion
uut : entity work.sum
   generic map (
      BASE_ADDR         => SUM_IB_BASE,
      IFCS              => IFCS,
      BLOCK_SIZE        => BLOCK_SIZE,
      DMA_DATA_WIDTH    => DMA_DATA_WIDTH,
      DMA_ID            => "11",
      NFIFO_LUT_MEMORY  => false
   )
   port map (
      -- Common signals
      CLK      => CLK,
      RESET    => RESET,

      INTERRUPT    => interrupt,
      IDLE         => idle,
      FLUSH        => flush,
      INIT         => init,
      -- Data interface
      -- Read interface
      IB_RD_ADDR     => ib_rd.ADDR,
      IB_RD_DATA     => ib_rd.DATA,
      IB_RD_BE       => ib_rd.BE,
      IB_RD_REQ      => ib_rd.REQ,
      IB_RD_ARDY     => ib_rd.ARDY,
      IB_RD_SRC_RDY  => ib_rd.SRC_RDY,

      -- BM interface
      -- Memory interface
      DMA_ADDR        => dma_addr,
      DMA_DOUT        => dma_dout,
      DMA_REQ         => dma_req,
      DMA_ACK         => dma_ack,
      DMA_DONE        => dma_done,
      DMA_TAG         => dma_tag,

      -- SW memory interface
      MI_SW_DWR      => mi32.DWR,
      MI_SW_ADDR     => mi32.ADDR,
      MI_SW_RD       => mi32.RD,
      MI_SW_WR       => mi32.WR,
      MI_SW_BE       => mi32.BE,
      MI_SW_DRD      => mi32.DRD,
      MI_SW_ARDY     => mi32.ARDY,
      MI_SW_DRDY     => mi32.DRDY,

      -- RxReqFifo interface
      RX_RF_RADDR   => rx_rf_raddr,
      RX_RF_DOUT    => rx_rf_dout,
      RX_RF_DVLD    => rx_rf_dvld,
      RX_RF_EMPTY   => rx_rf_empty,
      RX_RF_READ    => rx_rf_read,
      RX_RF_STATUS  => rx_rf_status,

      -- Rx status update
      RX_SU_ADDR     => rx_su_addr,
      RX_SU_DATA     => rx_su_data,
      RX_SU_DVLD     => rx_su_dvld,
      RX_SU_HFULL    => rx_su_hfull,

      -- Tx status update
      TX_SU_ADDR     => tx_su_addr,
      TX_SU_DATA     => tx_su_data,
      TX_SU_DVLD     => tx_su_dvld,
      TX_SU_HFULL    => tx_su_hfull

   );

DMA2BM_U: entity work.DMA2BM
   generic map (
      DMA_DATA_WIDTH => DMA_DATA_WIDTH
   )
   port map (
      CLK            => CLK,
      RESET          => RESET,

      -- Memory interface
      DMA_ADDR        => dma_addr,
      DMA_DOUT        => dma_dout,
      DMA_REQ         => dma_req,
      DMA_ACK         => dma_ack,
      DMA_DONE        => dma_done,
      DMA_TAG         => dma_tag,

      -- Bus master interface
      BM_GLOBAL_ADDR  => ib_bm.global_addr,
      BM_LOCAL_ADDR   => ib_bm.local_addr,
      BM_LENGTH       => ib_bm.length,
      BM_TAG          => ib_bm.tag,
      bM_TRANS_TYPE   => ib_bm.trans_type,
      BM_REQ          => ib_bm.req,
      bM_ACK          => ib_bm.ack,
      -- Output
      BM_OP_TAG       => ib_bm.op_tag,
      BM_OP_DONE      => ib_bm.op_done

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

flush          <= (others => '0');
init           <= (others => '0');
rx_rf_status   <= (others => '1');
rx_rf_empty    <= (others => '0');
rx_rf_dout     <= (rx_rf_dout'length-1 downto 64 => '1') & 
                     X"0000DEAD" & X"00000040";


-- register reg_rx_rf_read ------------------------------------------------------
reg_rx_rf_readp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         reg_rx_rf_read <= '0';
      elsif (mozes = '1') then
         reg_rx_rf_read <= rx_rf_read;
      end if;
   end if;
end process;

rx_rf_dvld  <= reg_rx_rf_read;


-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb : process
-- ----------------------------------------------------------------
--                    Procedures declaration
-- ----------------------------------------------------------------
-- ----------------------------------------------------------------


begin
--   InitMemory(256, "desc_data.txt", IbCmd);
   mozes <= '0';
   rx_su_addr <= (others => '0');
   rx_su_data <= (others => '0');
   rx_su_dvld <= '0';
   tx_su_addr <= (others => '0');
   tx_su_data <= (others => '0');
   tx_su_dvld <= '0';

   RESET <= '1', '0' after 100 ns;
   wait for 1 us;

   -- register access
   -- set interrupt register for channel 0 == rx0
--   SendLocalWrite(SUM_MI_BASE + 16#010#, X"00000000", 4, 16#ABCD#, X"00000000" & X"10000000", IbCmd);

   -- set txGaddr register
   SendLocalWrite(SUM_MI_BASE + 16#018#, X"00000000", 4, 16#ABCD#, X"00000000" & X"00000000", IbCmd);
   SendLocalWrite(SUM_MI_BASE + 16#01C#, X"00000000", 4, 16#ABCD#, X"00000000" & X"0000DEAD", IbCmd);

   -- read interrupt status register
--    SendLocalRead(SUM_MI_BASE + 16#014#, X"DEADBEEF", 4, 123, IbCmd);

   wait for 1 us;
   mozes <= '1';

   rx_su_addr <= (others => '0');
   rx_su_data <= X"01" & X"0056";
   rx_su_dvld <= '1';
   wait for CLKPER;
   rx_su_dvld <= '0';

   tx_su_addr <= (others => '0');
   tx_su_data <= X"01";
   tx_su_dvld <= '1';
   wait for CLKPER;
   tx_su_dvld <= '0';


   wait;
end process;


end architecture behavioral;
