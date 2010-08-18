-- dma_module_wrapper.vhd: DMA module without PCIe wrapper
-- Copyright (C) 2009 CESNET
-- Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
--            Martin Spinler <xspinl00@stud.fit.vutbr.cz>
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

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.combov2_nc_const.all;
use work.math_pack.all;
use work.ib_pkg.all;
use work.lb_pkg.all;
use work.fl_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity dma_module_wrapper is
   generic(DMA_IFC_COUNT : integer := 4;
            DATA_WIDTH : integer := 16
          );
port (
  -- common interface
  CLK         : in  std_logic;
  RESET       : in  std_logic;

  -- misc signals
  RX_INTERRUPT   : out std_logic;
  TX_INTERRUPT   : out std_logic;
    
  -- Read interface (FrameLinks)
  TX_DATA        : out std_logic_vector(DMA_IFC_COUNT*DATA_WIDTH-1 downto 0);
  TX_SOF_N       : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  TX_SOP_N       : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  TX_EOP_N       : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  TX_EOF_N       : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  TX_REM         : out std_logic_vector(log2(DATA_WIDTH/8)*DMA_IFC_COUNT-1 downto 0);
  TX_SRC_RDY_N   : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  TX_DST_RDY_N   : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  
  -- Write interface (FrameLinks)
  RX_DATA        : in  std_logic_vector(DMA_IFC_COUNT*DATA_WIDTH-1 downto 0);
  RX_SOF_N       : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  RX_SOP_N       : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  RX_EOP_N       : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  RX_EOF_N       : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  RX_REM         : in  std_logic_vector(log2(DATA_WIDTH/8)*DMA_IFC_COUNT-1 downto 0);
  RX_SRC_RDY_N   : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  RX_DST_RDY_N   : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  
  -- Upstream InternalBus
  UP_DATA        : out std_logic_vector(63 downto 0);
  UP_SOP_N       : out std_logic;
  UP_EOP_N       : out std_logic;
  UP_SRC_RDY_N   : out std_logic;
  UP_DST_RDY_N   : in  std_logic;
  
  -- Downstream InternalBus
  DOWN_DATA      : in  std_logic_vector(63 downto 0);
  DOWN_SOP_N     : in  std_logic;
  DOWN_EOP_N     : in  std_logic;
  DOWN_SRC_RDY_N : in  std_logic;
  DOWN_DST_RDY_N : out std_logic
);
end entity dma_module_wrapper;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of dma_module_wrapper is

  -- Internal Bus signals
  signal ibus0      : t_internal_bus64;  -- to DMA_MODULE_WRAPPER
  signal ibus1      : t_internal_bus64;  -- to IB2LB
  signal ibus2      : t_internal_bus64;  -- to DMA_MODULE
  
  -- Local Bus signals
  signal lbus0      : t_local_bus16;     -- to DMA_MODULE

begin
 
  -- DMA MODULE 4x16b RXTX ----------------------------------------------------------
  DMA_MODULE_I: entity work.DMA_MODULE_GEN_TU
  generic map(
   RX_IFC_COUNT        => 4,
   RX_BUFFER_SIZE      => 4096,
   RX_FL_WIDTH         => 64,

   TX_IFC_COUNT        => 4,
   TX_BUFFER_SIZE      => 4096,
   TX_FL_WIDTH         => 64,

   RX_DISCARD_EN       => false
  )
  port map(
     -- Common Interface
     CLK              => CLK,
     RESET            => RESET,
     
     RX_INTERRUPT     => RX_INTERRUPT,
     TX_INTERRUPT     => TX_INTERRUPT,
     
     -- network interfaces
     -- input FrameLink interfaces
      TX_DATA         => TX_DATA,
      TX_SOF_N        => TX_SOF_N,
      TX_SOP_N        => TX_SOP_N,
      TX_EOP_N        => TX_EOP_N,
      TX_EOF_N        => TX_EOF_N,
      TX_REM          => TX_REM,
      TX_SRC_RDY_N    => TX_SRC_RDY_N,
      TX_DST_RDY_N    => TX_DST_RDY_N,
  
  -- Write interface (FrameLinks)
      RX_DATA         => RX_DATA,
      RX_SOF_N        => RX_SOF_N,
      RX_SOP_N        => RX_SOP_N,
      RX_EOP_N        => RX_EOP_N,
      RX_EOF_N        => RX_EOF_N,
      RX_REM          => RX_REM,
      RX_SRC_RDY_N    => RX_SRC_RDY_N,
      RX_DST_RDY_N    => RX_DST_RDY_N,

      UP_DATA         => ibus2.up.data,
      UP_SOP_N        => ibus2.up.sop_n,
      UP_EOP_N        => ibus2.up.eop_n,
      UP_SRC_RDY_N    => ibus2.up.src_rdy_n,
      UP_DST_RDY_N    => ibus2.up.dst_rdy_n,
  
  -- Downstream InternalBus
      DOWN_DATA       => ibus2.down.data,
      DOWN_SOP_N      => ibus2.down.sop_n,
      DOWN_EOP_N      => ibus2.down.eop_n,
      DOWN_SRC_RDY_N  => ibus2.down.src_rdy_n,
      DOWN_DST_RDY_N  => ibus2.down.dst_rdy_n,

     -- Local Bus interface
      LB_DWR          => lbus0.dwr,
      LB_BE           => lbus0.be,
      LB_ADS_N        => lbus0.ads_n,
      LB_RD_N         => lbus0.rd_n,
      LB_WR_N         => lbus0.wr_n,
      LB_DRD          => lbus0.drd,
      LB_RDY_N        => lbus0.rdy_n,
      LB_ERR_N        => lbus0.err_n,
      LB_ABORT_N      => lbus0.abort_n
  ); 

  -- -------------------------------------------------------------------------
  --                         INTERCONNECTION SYSTEM 
  -- -------------------------------------------------------------------------
  -- Internal Bus Switch 0  --------------------------------------------------
  IB_SWITCH0_I: entity work.IB_SWITCH
  generic map(
     -- Data Width (64/128)
     DATA_WIDTH        => 64,
     -- Port 0 Address Space 
     SWITCH_BASE       => X"00000000",
     SWITCH_LIMIT      => X"C4000000",
     -- Port 1 Address Space
     DOWNSTREAM0_BASE  => X"00000000",
     DOWNSTREAM0_LIMIT => X"02000000",
     -- Port 2 Address Space
     DOWNSTREAM1_BASE  => X"02000000",
     DOWNSTREAM1_LIMIT => X"C2000000"
  )  
  port map(
     -- Common Interface
     IB_CLK               => CLK,
     IB_RESET             => RESET,
     -- Upstream Port
     PORT0                => ibus0,   
     -- Downstream Ports
     PORT1                => ibus1,
     PORT2                => ibus2
  ); 
  
  ibus0.DOWN.DATA       <= DOWN_DATA;
  ibus0.DOWN.SOP_N      <= DOWN_SOP_N;  
  ibus0.DOWN.EOP_N      <= DOWN_EOP_N;
  ibus0.DOWN.SRC_RDY_N  <= DOWN_SRC_RDY_N;
  DOWN_DST_RDY_N        <= ibus0.DOWN.DST_RDY_N;
  
  UP_DATA               <= ibus0.UP.DATA;
  UP_SOP_N              <= ibus0.UP.SOP_N;
  UP_EOP_N              <= ibus0.UP.EOP_N;
  UP_SRC_RDY_N          <= ibus0.UP.SRC_RDY_N;
  ibus0.UP.DST_RDY_N    <= UP_DST_RDY_N;
     
  -- IB2LB -------------------------------------------------------------------
  IB2LB_I: entity work.LB_ROOT
  generic map(
     BASE_ADDR     => X"00000000",
     LIMIT         => X"02000000"
  )  
  port map(
     -- Common Interface
     IB_CLK        => CLK,
     RESET         => RESET,
     -- Local Bus Interface
     INTERNAL_BUS  => ibus1,
     -- Local Bus Interface
     LOCAL_BUS     => lbus0
  ); 
  
end architecture full;
