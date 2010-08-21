--
-- dma_test.vhd: DMA modul for PCIe2IB testing
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
use work.ib_pkg.all;
use work.lb_pkg.all;
use work.dma_test_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity DMA_TEST is
   port(
      -- Common Interface
      CLK           : in  std_logic;
      RESET         : in  std_logic;
      
      -- Internal Bus Interface
      INTERNAL_BUS  : inout t_internal_bus64;

      -- Interrupt System
      INTERRUPT     : out std_logic;
      INTR_DATA     : out std_logic_vector(4 downto 0);
      INTR_RDY      : in  std_logic
      );
end entity DMA_TEST;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture DMA_TEST_ARCH of DMA_TEST is
 
     -- Internal Bus Switch 
     signal ib_switch_1    : t_internal_bus64;
     signal ib_switch_2    : t_internal_bus64;

     -- Local Bus Root
     signal lb_root_16     : t_local_bus16;

     -- Internal Bus Endpoint 
     signal ib_ep_wr_addr      : std_logic_vector(31 downto 0);       -- Address
     signal ib_ep_wr_data      : std_logic_vector(63 downto 0);       -- Data
     signal ib_ep_wr_be        : std_logic_vector(7 downto 0);        -- Byte Enable
     signal ib_ep_wr_req       : std_logic;                           -- Write Request
     signal ib_ep_wr_rdy       : std_logic;                           -- Ready

     signal ib_ep_rd_addr      : std_logic_vector(31 downto 0);       -- Address
     signal ib_ep_rd_be        : std_logic_vector(7 downto 0);        -- Byte Enable
     signal ib_ep_rd_req       : std_logic;                           -- Read Request
     signal ib_ep_rd_ardy      : std_logic;                           -- Address Ready
     signal ib_ep_rd_data      : std_logic_vector(63 downto 0);       -- Read Data
     signal ib_ep_rd_src_rdy   : std_logic;                           -- Data Ready
     signal ib_ep_rd_dst_rdy   : std_logic;  

     signal ib_ep_wr       : t_ibmi_write64;
     signal ib_ep_rd       : t_ibmi_read64s;
     signal ib_ep_bm       : t_ibbm_64; 
     
     -- Local Bus Endpoint 
     signal lb_ep_mi32     : t_mi32;  


   -- CHIPSCOPE stuff ---------------------------------------------------------

--    component icon_ib
--      PORT (
--        CONTROL0 : INOUT STD_LOGIC_VECTOR(35 DOWNTO 0);
--        CONTROL1 : INOUT STD_LOGIC_VECTOR(35 DOWNTO 0));
--    
--    end component;
-- 
--    component ila_ib_up
--      PORT (
--        CONTROL : INOUT STD_LOGIC_VECTOR(35 DOWNTO 0);
--        CLK : IN STD_LOGIC;
--        DATA : IN STD_LOGIC_VECTOR(67 DOWNTO 0);
--        TRIG0 : IN STD_LOGIC_VECTOR(3 DOWNTO 0));
--    
--    end component;
-- 
--    component ila_ib_down
--      PORT (
--        CONTROL : INOUT STD_LOGIC_VECTOR(35 DOWNTO 0);
--        CLK : IN STD_LOGIC;
--        DATA : IN STD_LOGIC_VECTOR(67 DOWNTO 0);
--        TRIG0 : IN STD_LOGIC_VECTOR(3 DOWNTO 0));
--    
--    end component;
-- 
--    signal CONTROL0 : STD_LOGIC_VECTOR(35 DOWNTO 0);
--    signal CONTROL1 : STD_LOGIC_VECTOR(35 DOWNTO 0);
-- 
--    signal ila_ib_up_data   : std_logic_vector(67 downto 0);
--    signal ila_ib_down_data : std_logic_vector(67 downto 0);
-- 
--    signal ila_ib_up_trig   : std_logic_vector(3 downto 0);
--    signal ila_ib_down_trig : std_logic_vector(3 downto 0);
-- 
-- 
--    attribute dont_touch                : boolean;
--    attribute dont_touch of icon_ib     : component is TRUE;
--    attribute dont_touch of ila_ib_up   : component is TRUE;
--    attribute dont_touch of ila_ib_down : component is TRUE;

   -- -------------------------------------------------------------------------

begin

-- -- Internal Bus Switch -----------------------------------------------------
IB_SWITCH_U : entity work.IB_SWITCH
   generic map (
      -- Data Width
      DATA_WIDTH         => IB_DATA_WIDTH,
      -- Port 0 Address Space
      SWITCH_BASE        => IB_SWITCH_BASE,
      SWITCH_LIMIT       => IB_SWITCH_LIMIT,
      -- Port 1 Address Space
      DOWNSTREAM0_BASE   => DOWNSTREAM0_BASE,
      DOWNSTREAM0_LIMIT  => DOWNSTREAM0_LIMIT,
      -- Port 2 Address Space
      DOWNSTREAM1_BASE   => DOWNSTREAM1_BASE, 
      DOWNSTREAM1_LIMIT  => DOWNSTREAM1_LIMIT
   )

   port map (
      -- Common Interface
      IB_CLK         => CLK,
      IB_RESET       => RESET,
      -- Upstream Port
      PORT0          => INTERNAL_BUS,
      -- Downstream Ports
      PORT1          => ib_switch_1,
      PORT2          => ib_switch_2
   );

-- -- Internal Bus to Local Bus Bridge ----------------------------------------
LB_ROOT_U : entity work.LB_ROOT
   generic map (
      BASE_ADDR      => LB_ROOT_BASE,
      LIMIT          => LB_ROOT_LIMIT
   )
   port map (
      -- Common Interface
      IB_CLK         => CLK,
      RESET          => RESET,

      -- Internal Bus Interface
      INTERNAL_BUS   => ib_switch_1,

      -- Local Bus Interface
      LOCAL_BUS      => lb_root_16
  );

-- -- Internal Bus Endpoint Component with BM ---------------------------------
IB_ENDPOINT_U: entity work.IB_ENDPOINT_MASTER_NOREC
   generic map (
      LIMIT                => IB_EP_LIMIT,
      INPUT_BUFFER_SIZE    => IB_EP_INPUT_BUFFER_SIZE,
      OUTPUT_BUFFER_SIZE   => IB_EP_OUTPUT_BUFFER_SIZE,
      READ_REORDER_BUFFER  => IB_EP_READ_REORDER_BUFFER,
      STRICT_EN            => IB_EP_STRICT_EN
   )
   port map (
      -- Common Interface
      IB_CLK         => CLK,
      IB_RESET       => RESET,

      -- Internal Bus Interface
      -- DOWNSTREAM
      IB_DOWN_DATA         => ib_switch_2.DOWN.DATA,
      IB_DOWN_SOP_N        => ib_switch_2.DOWN.SOP_N,
      IB_DOWN_EOP_N        => ib_switch_2.DOWN.EOP_N,
      IB_DOWN_SRC_RDY_N    => ib_switch_2.DOWN.SRC_RDY_N,
      IB_DOWN_DST_RDY_N    => ib_switch_2.DOWN.DST_RDY_N,
        -- UPSTREAM
      IB_UP_DATA           => ib_switch_2.UP.DATA,
      IB_UP_SOP_N          => ib_switch_2.UP.SOP_N,
      IB_UP_EOP_N          => ib_switch_2.UP.EOP_N,
      IB_UP_SRC_RDY_N      => ib_switch_2.UP.SRC_RDY_N,
      IB_UP_DST_RDY_N      => ib_switch_2.UP.DST_RDY_N,

       -- User Component Write Interface
      WR_ADDR              => ib_ep_wr_addr,
      WR_DATA              => ib_ep_wr_data,
      WR_BE                => ib_ep_wr_be,
      WR_REQ               => ib_ep_wr_req,
      WR_RDY               => ib_ep_wr_rdy,

      -- Read Interface
      -- Input Interface
      RD_ADDR              => ib_ep_rd_addr,  
      RD_BE                => ib_ep_rd_be,    
      RD_REQ               => ib_ep_rd_req,  
      RD_ARDY              => ib_ep_rd_ardy, 
      -- Output Interface
      RD_DATA              => ib_ep_rd_data, 
      RD_SRC_RDY           => ib_ep_rd_src_rdy,
      RD_DST_RDY           => ib_ep_rd_dst_rdy,

      -- Master Interface Input
      BM_GLOBAL_ADDR       => ib_ep_bm.GLOBAL_ADDR,   
      BM_LOCAL_ADDR        => ib_ep_bm.LOCAL_ADDR,    
      BM_LENGTH            => ib_ep_bm.LENGTH,        
      BM_TAG               => ib_ep_bm.TAG,           
      BM_TRANS_TYPE        => ib_ep_bm.TRANS_TYPE,    
      BM_REQ               => ib_ep_bm.REQ,           
      BM_ACK               => ib_ep_bm.ACK,           

      -- Master Output interface
      BM_OP_TAG            => ib_ep_bm.OP_TAG,        
      BM_OP_DONE           => ib_ep_bm.OP_DONE       
   );

-- -- Local Bus Endpoint ------------------------------------------------------   
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
      LB_CLK         => CLK,
      LOCALBUS       => lb_root_16,

      -- User Component Interface
      CLK            => CLK,
      MI32           => lb_ep_mi32
  );

-- -- MI32 to BM Unit ---------------------------------------------------------
MI32TOBM_U : entity work.MI32TOBM
   port map (
      -- Common interface
      RESET          => RESET,
      CLK            => CLK,
      -- MI32 interface
      MI32           => lb_ep_mi32,
      -- Endpoint Busmaster interface
      BM             => ib_ep_bm
      );

-- -- Internal Bus User Component (Memory) ------------------------------------
IBMI64MEM_U : entity work.IBMI64MEM_NOREC
   generic map (
      SIZE           => IB_MEM_SIZE,
      BRAM_DISTMEM   => IB_MEM_TYPE 
    )
   port map (
      -- Common Interface
      CLK            => CLK,
      RESET          => RESET,
     -- IBMI_WRITE64     => ib_ep_wr,
     -- IBMI_READ64      => ib_ep_rd 

      -- IBMI64 Interface
      WRITE_ADDR     => ib_ep_wr_addr,
      WRITE_DATA     => ib_ep_wr_data,
      WRITE_BE       => ib_ep_wr_be,
      WRITE_REQ      => ib_ep_wr_req,
      WRITE_RDY      => ib_ep_wr_rdy,

      READ_ADDR      => ib_ep_rd_addr, 
      READ_BE        => ib_ep_rd_be, 
      READ_REQ       => ib_ep_rd_req, 
      READ_ARDY      => ib_ep_rd_ardy, 
      READ_DATA      => ib_ep_rd_data, 
      READ_SRC_RDY   => ib_ep_rd_src_rdy, 
      READ_DST_RDY   => ib_ep_rd_dst_rdy 
   );

-- -- Interrupt System --------------------------------------------------------
   -- unconnected
   INTERRUPT <= '0';
   INTR_DATA <= "00000";


   -- CHIPSCOPE stuff ---------------------------------------------------------

--    ICON_IB_I : icon_ib
--    port map (
--       CONTROL0 => CONTROL0,
--       CONTROL1 => CONTROL1
--    );
-- 
--    ILA_UP_I : ila_ib_up
--    port map (
--       CONTROL => CONTROL0,
--       CLK => CLK,
--       DATA => ila_ib_up_data,
--       TRIG0 => ila_ib_up_trig
--    );
-- 
--    ILA_DOWN_I : ila_ib_down
--    port map (
--       CONTROL => CONTROL1,
--       CLK => CLK,
--       DATA => ila_ib_down_data,
--       TRIG0 => ila_ib_down_trig
--    );
-- 
--    ila_ib_up_data    <= INTERNAL_BUS.UP.DATA & 
--                         INTERNAL_BUS.UP.SOP_N & 
--                         INTERNAL_BUS.UP.EOP_N & 
--                         INTERNAL_BUS.UP.SRC_RDY_N & 
--                         INTERNAL_BUS.UP.DST_RDY_N;  
-- 
--    ila_ib_down_data <=  INTERNAL_BUS.DOWN.DATA & 
--                         INTERNAL_BUS.DOWN.SOP_N & 
--                         INTERNAL_BUS.DOWN.EOP_N & 
--                         INTERNAL_BUS.DOWN.SRC_RDY_N & 
--                         INTERNAL_BUS.DOWN.DST_RDY_N;
-- 
--    ila_ib_up_trig    <= INTERNAL_BUS.UP.SOP_N & 
--                         INTERNAL_BUS.UP.EOP_N & 
--                         INTERNAL_BUS.UP.SRC_RDY_N & 
--                         INTERNAL_BUS.UP.DST_RDY_N;
-- 
--    ila_ib_down_trig  <= INTERNAL_BUS.DOWN.SOP_N & 
--                         INTERNAL_BUS.DOWN.EOP_N & 
--                         INTERNAL_BUS.DOWN.SRC_RDY_N & 
--                         INTERNAL_BUS.DOWN.DST_RDY_N;

end architecture DMA_TEST_ARCH;

