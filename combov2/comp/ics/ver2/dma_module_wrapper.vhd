-- dma_module_wrapper.vhd: DMA module without PCIe wrapper
-- Copyright (C) 2009 CESNET
-- Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
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
use work.dma_mod_4x16b_rxtx_const.all;
use work.math_pack.all;
use work.ib_pkg.all;
use work.lb_pkg.all;
use work.fl_pkg.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity dma_module_wrapper is
   generic (DMA_IFC_COUNT : integer := 4;
      DATA_WIDTH : integer := 16);
port (
  -- common interface
  CLK         : in  std_logic;
  RESET       : in  std_logic;

  -- misc signals
  RX_INTERRUPT   : out std_logic;
  TX_INTERRUPT   : out std_logic;
    
  -- Read interface (FrameLinks)
  TX_DATA        : out std_logic_vector(DATA_WIDTH*DMA_IFC_COUNT-1 downto 0);
  TX_SOF_N       : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  TX_SOP_N       : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  TX_EOP_N       : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  TX_EOF_N       : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  TX_REM         : out std_logic_vector((log2(DATA_WIDTH/8)*DMA_IFC_COUNT)-1 downto 0);
  TX_SRC_RDY_N   : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  TX_DST_RDY_N   : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  
  -- Write interface (FrameLinks)
  RX_DATA        : in  std_logic_vector(DATA_WIDTH*DMA_IFC_COUNT-1 downto 0);
  RX_SOF_N       : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  RX_SOP_N       : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  RX_EOP_N       : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  RX_EOF_N       : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
  RX_REM         : in  std_logic_vector((log2(DATA_WIDTH/8)*DMA_IFC_COUNT)-1 downto 0);
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
  signal ibus2      : t_internal_bus64;  -- to DMA_MOD_4x16b_RXTX
  
  -- Local Bus signals
  signal lbus0      : t_local_bus16;     -- to DMA_MOD_4x16b_RXTX
begin
 
  -- DMA MODULE 4x16b RXTX ----------------------------------------------------------
  --DMA_MOD_4x16b_RXTX_I: entity work.DMA_MOD_4x16b_RXTX
  DMA_MOD_4x16b_RXTX_I: entity work.rxtx_buffers_opt_norec
  generic map(
      NET_IFC_COUNT           => 4,
      DATA_WIDTH              => 16,
      BLOCK_SIZE              => RXTX_BLOCK_SIZE,
      RXTXBUF_IFC_TOTAL_SIZE  => RXTX_IFC_TOTAL_SIZE,

      -- DMA Controller generics
      BUFFER_ADDR             => RXTX_BUFFER_ADDR,
      BUFFER_SIZE             => RXTX_BUFFER_SIZE,
      DESC_BASE_ADDR          => RXTX_DESC_BASE_ADDR,
      IB_EP_LIMIT             => IB_LIMIT,
      LB_EP_BASE_ADDR         => LB_BASE_ADDR,
      LB_EP_LIMIT             => LB_LIMIT
  )
  port map(
     -- Common Interface
     CLK              => CLK,
     RESET            => RESET,
     
     RX_INTERRUPT     => RX_INTERRUPT,
     TX_INTERRUPT     => TX_INTERRUPT,

     -- Read interface (FrameLinks)
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
  
     -- Upstream InternalBus
     IB_UP_DATA         => ibus2.UP.DATA,
     IB_UP_SOP_N        => ibus2.UP.SOP_N,
     IB_UP_EOP_N        => ibus2.UP.EOP_N,
     IB_UP_SRC_RDY_N    => ibus2.UP.SRC_RDY_N,
     IB_UP_DST_RDY_N    => ibus2.UP.DST_RDY_N,
  
    -- Downstream InternalBus
     IB_DOWN_DATA       => ibus2.DOWN.DATA,
     IB_DOWN_SOP_N      => ibus2.DOWN.SOP_N,
     IB_DOWN_EOP_N      => ibus2.DOWN.EOP_N,
     IB_DOWN_SRC_RDY_N  => ibus2.DOWN.SRC_RDY_N,
     IB_DOWN_DST_RDY_N  => ibus2.DOWN.DST_RDY_N, 
         
     LB_DWR            => lbus0.DWR,
     LB_BE             => lbus0.BE,
     LB_ADS_N          => lbus0.ADS_N,
     LB_RD_N           => lbus0.RD_N,
     LB_WR_N           => lbus0.WR_N,
     LB_DRD            => lbus0.DRD,
     LB_RDY_N          => lbus0.RDY_N,
     LB_ERR_N          => lbus0.ERR_N,
     LB_ABORT_N        => lbus0.ABORT_N
    ); 
     
  -- -------------------------------------------------------------------------
  --                         INTERCONNECTION SYSTEM 
  -- -------------------------------------------------------------------------
  -- Internal Bus Switch 0  --------------------------------------------------
  IB_SWITCH0_I: entity work.IB_SWITCH
  generic map(
     -- Data Width (64/128)
     DATA_WIDTH        => IBS0_DATA_WIDTH,
     -- Port 0 Address Space 
     SWITCH_BASE       => IBS0_SWITCH_BASE,
     SWITCH_LIMIT      => IBS0_SWITCH_LIMIT,
     -- Port 1 Address Space
     DOWNSTREAM0_BASE  => IBS0_DOWNSTREAM0_BASE,
     DOWNSTREAM0_LIMIT => IBS0_DOWNSTREAM0_LIMIT,
     -- Port 2 Address Space
     DOWNSTREAM1_BASE  => IBS0_DOWNSTREAM1_BASE,
     DOWNSTREAM1_LIMIT => IBS0_DOWNSTREAM1_LIMIT
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
     BASE_ADDR     => IB2LB_BASE_ADDR,
     LIMIT         => IB2LB_LIMIT
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
