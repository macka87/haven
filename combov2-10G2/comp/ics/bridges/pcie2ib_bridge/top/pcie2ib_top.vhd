--
-- pcie2ib_top.vhd : PCI-Express endpoint block plus and PCIE2IB bridge wrapper
--                   for the Xilinx ML555 board
-- Copyright (C) 2007 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use work.pcie_pkg.all; 
use work.ib_pkg.all; 

-- pragma translate_off
library UNISIM;
use UNISIM.vcomponents.all;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                   ENTITY DECLARATION -- PCIe2IB TOP                       --
-- ---------------------------------------------------------------------------- 

entity PCIE2IB_TOP is
   generic (
      -- PCIe endpoint block plus generic interface ---------------------------
      FAST_TRAIN_SIMULATION_ONLY : std_logic;                           -- Don't assert when using the core in HW!!!
      -- PCIe to IB bridge generic interface ----------------------------------
      IB_BASE_ADDR     : std_logic_vector(31 downto 0) := X"0F000000"; -- IB Base Address
      LTAG_WIDTH       : integer :=   5;                               -- 'Local Read' Buffer tag width (max. 7)
      GTAG_WIDTH       : integer :=   5;                               -- 'Global Read' Buffer tag width (max. 7)       
      BAR_HIT_MASK     : std_logic_vector( 6 downto 0) :=   "1111111"; -- Base Address Register hit mask
      -- BAR base addresses
      BAR0_BASE        : std_logic_vector(31 downto 0) := X"01000000"; -- BAR0 base address for PCIE->IB transalation
      BAR1_BASE        : std_logic_vector(31 downto 0) := X"02000000"; -- BAR1 base address for PCIE->IB transalation
      BAR2_BASE        : std_logic_vector(31 downto 0) := X"03000000"; -- BAR2 base address for PCIE->IB transalation
      BAR3_BASE        : std_logic_vector(31 downto 0) := X"04000000"; -- BAR3 base address for PCIE->IB transalation
      BAR4_BASE        : std_logic_vector(31 downto 0) := X"06000000"; -- BAR4 base address for PCIE->IB transalation
      BAR5_BASE        : std_logic_vector(31 downto 0) := X"08000000"; -- BAR5 base address for PCIE->IB transalation       
      BAR6_BASE        : std_logic_vector(31 downto 0) := X"0A000000"; -- ROM  base address for PCIE->IB transalation
      -- BAR base addresses masks
      BAR0_MASK        : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR0 mask for PCIE->IB transalation
      BAR1_MASK        : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR1 mask for PCIE->IB transalation
      BAR2_MASK        : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR2 mask for PCIE->IB transalation
      BAR3_MASK        : std_logic_vector(31 downto 0) := X"01FFFFFF"; -- BAR3 mask for PCIE->IB transalation
      BAR4_MASK        : std_logic_vector(31 downto 0) := X"01FFFFFF"; -- BAR4 mask for PCIE->IB transalation
      BAR5_MASK        : std_logic_vector(31 downto 0) := X"01FFFFFF"; -- BAR5 mask for PCIE->IB transalation       
      BAR6_MASK        : std_logic_vector(31 downto 0) := X"01FFFFFF"  -- ROM  mask for PCIE->IB transalation           
   );
   port (
      -- PCI Express interface ------------------------------------------------
      PCIE_RST_N  : in std_logic;                     -- PCI-E bus reset
      PCIE_CLK    : in std_logic;                     -- PCI-E reference clock
      
      PCI_EXP_TXN : out std_logic_vector(3 downto 0); -- PCI-E serial data inputs&outputs (RocketIO)
      PCI_EXP_TXP : out std_logic_vector(3 downto 0); -- PCI-E serial data inputs&outputs (RocketIO)
      PCI_EXP_RXN : in  std_logic_vector(3 downto 0); -- PCI-E serial data inputs&outputs (RocketIO)
      PCI_EXP_RXP : in  std_logic_vector(3 downto 0); -- PCI-E serial data inputs&outputs (RocketIO)
      
      -- Internal Bus interface -----------------------------------------------
      IB_RST     : out std_logic;                     -- IB reset
      IB_CLK     : out std_logic;                     -- IB clock

      IB          : inout t_internal_bus64;           -- IB interface
      BM          : inout t_ibbm_64;                  -- Bus Master control interface 
      -- Control -- Chipscope "control" signal
      CONTROL     : out std_logic_vector(35 downto 0)
   );
end PCIE2IB_TOP;

-- ----------------------------------------------------------------------------
--                   ARCHITECTURE DECLARATION -- PCIe2IB TOP                 --
-- ---------------------------------------------------------------------------- 

architecture STRUCTURAL of PCIE2IB_TOP is

   -- -------------------------------------------------------------------------
   --                           Component declaration                        --
   -- -------------------------------------------------------------------------    

   component endpoint_blk_plus_v1_3
      port (
         -- 
         FAST_TRAIN_SIMULATION_ONLY : in std_logic;      
         TWO_PLM_AUTO_CONFIG    : in  std_logic_vector( 1 downto 0);      
         -- System interface
         SYS_RESET_N            : in std_logic;
         SYS_CLK                : in std_logic;
         -- Transaction interface 
         TRN_CLK                : out std_logic;
         TRN_RESET_N            : out std_logic;
         TRN_LNK_UP_N           : out std_logic;      
         -- Receive --
         TRN_RBAR_HIT_N         : out std_logic_vector( 6 downto 0); -- BAR hit
         TRN_RSRC_RDY_N         : out std_logic; -- Source ready
         TRN_RDST_RDY_N         : in  std_logic; -- Destination ready
         TRN_RSOF_N             : out std_logic; -- Start of Frame
         TRN_REOF_N             : out std_logic; -- End of Frame
         TRN_RNP_OK_N           : in  std_logic; -- Ready to accept Non-posted request
         TRN_RSRC_DSC_N         : out std_logic; -- Discontinue - packet abort
         TRN_RERRFWD_N          : out std_logic; -- Error forward - packet bad
         TRN_RD                 : out std_logic_vector(63 downto 0); -- Data
         TRN_RREM_N             : out std_logic_vector( 7 downto 0); -- Data reminder
         TRN_RFC_NPH_AV         : out std_logic_vector( 7 downto 0); -- Non-posted Header Flow Credits Available  
         TRN_RFC_NPD_AV         : out std_logic_vector(11 downto 0); -- Non-posted Data Flow Credits Available
         TRN_RFC_PH_AV          : out std_logic_vector( 7 downto 0); -- Posted Header Flow Credits Available
         TRN_RFC_PD_AV          : out std_logic_vector(11 downto 0); -- Posted Data Flow Credits Available
         TRN_RCPL_STREAMING_N   : in  std_logic;
         -- Transmit --
         TRN_TSOF_N             : in  std_logic; --        
         TRN_TEOF_N             : in  std_logic; --
         TRN_TSRC_RDY_N         : in  std_logic; --
         TRN_TDST_RDY_N         : out std_logic; --            
         TRN_TD                 : in  std_logic_vector(63 downto 0);      
         TRN_TREM_N             : in  std_logic_vector( 7 downto 0);
         TRN_TBUF_AV            : out std_logic_vector( 2 downto 0); -- Buffers available
         TRN_TSRC_DSC_N         : in  std_logic; -- TX source discontinue
         TRN_TDST_DSC_N         : out std_logic; -- TX destination discontinue
         TRN_TERRFWD_N          : in  std_logic;      
         -- Endpoint configuration
         CFG_BUS_NUMBER         : out std_logic_vector( 7 downto 0);
         CFG_DEVICE_NUMBER      : out std_logic_vector( 4 downto 0);
         CFG_FUNCTION_NUMBER    : out std_logic_vector( 2 downto 0);      
         -- 
         CFG_TO_TURNOFF_N       : out std_logic;
         CFG_ERR_POSTED_N       : in  std_logic;
         CFG_TRN_PENDING_N      : in  std_logic;
         CFG_ERR_CPL_TIMEOUT_N  : in  std_logic;
         CFG_INTERRUPT_N        : in std_logic;
         CFG_INTERRUPT_RDY_N    : out std_logic;
         CFG_ERR_UR_N           : in std_logic;
         CFG_RD_EN_N            : in std_logic;
         CFG_ERR_ECRC_N         : in std_logic;
         CFG_ERR_CPL_ABORT_N    : in std_logic;
         CFG_WR_EN_N            : in  std_logic;
         CFG_RD_WR_DONE_N       : out std_logic;
         CFG_ERR_COR_N          : in std_logic;
         CFG_ERR_CPL_UNEXPECT_N : in std_logic;
         CFG_PM_WAKE_N          : in std_logic;
         CFG_BYTE_EN_N          : in  std_logic_vector( 3 downto 0);
         CFG_ERR_TLP_CPL_HEADER : in  std_logic_vector(47 downto 0);
         CFG_LCOMMAND           : out std_logic_vector(15 downto 0);
         CFG_DSTATUS            : out std_logic_vector(15 downto 0);
         CFG_DSN                : in  std_logic_vector(63 downto 0);
         CFG_STATUS             : out std_logic_vector(15 downto 0);
         CFG_COMMAND            : out std_logic_vector(15 downto 0);
         CFG_DI                 : in  std_logic_vector(31 downto 0);
         CFG_DO                 : out std_logic_vector(31 downto 0);
         CFG_DWADDR             : in  std_logic_vector( 9 downto 0);
         CFG_DCOMMAND           : out std_logic_vector(15 downto 0);
         CFG_PCIE_LINK_STATE_N  : out std_logic_vector( 2 downto 0);
         CFG_LSTATUS            : out std_logic_vector(15 downto 0);
         -- PCI Express interface
         PCI_EXP_TXN            : out std_logic_vector( 3 downto 0);
         PCI_EXP_TXP            : out std_logic_vector( 3 downto 0);      
         PCI_EXP_RXN            : in  std_logic_vector( 3 downto 0);
         PCI_EXP_RXP            : in  std_logic_vector( 3 downto 0)
      );
   end component;      

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------    

   signal cfg_dcommand_4_0  : std_logic_vector( 4 downto 0);
   signal cfg_dcommand_15_8 : std_logic_vector(15 downto 8);
   -- PCI-E transaction interface (TRN)
   signal trn_clk     : std_logic; -- Clock
   signal trn_reset_n : std_logic; -- #Reset
   signal trn_lnk_up_n: std_logic; -- Link up
   signal trn_reset   : std_logic; -- Reset
   -- PCI-E configuration
   signal pcie_trn    : t_pcie_trn;       -- Xilinx PCI-E block core plus transaction bus
   signal pcie_cfg    : t_pcie_bridge_config;

begin

   -- -------------------------------------------------------------------------
   --                   Xilinx PCI-Express block plus logicore               --
   -- -------------------------------------------------------------------------  

   PCIE_BLK_PLUS_I: endpoint_blk_plus_v1_3
   port map (
      -- 
      FAST_TRAIN_SIMULATION_ONLY => FAST_TRAIN_SIMULATION_ONLY,
      TWO_PLM_AUTO_CONFIG    => "00",
      -- System interface
      SYS_RESET_N            => PCIE_RST_N,  -- System reset (cold, hot), active low
      SYS_CLK                => PCIE_CLK,    -- Reference clock, 100 or 250MHz
      -- Transaction interface
      TRN_CLK                => trn_clk,     -- out
      TRN_RESET_N            => trn_reset_n, -- out - (sys_rst OR NOT pll_lock OR gtp_lock_lost OR NOT dl_active_state)
      TRN_LNK_UP_N           => trn_lnk_up_n,        -- out
      -- Transaction Receive 
      TRN_RBAR_HIT_N         => pcie_trn.rx.bar_hit_n, -- BAR hit
      TRN_RSRC_DSC_N         => pcie_trn.rx.src_dsc_n, -- Discontinue - packet abort 
      TRN_RSRC_RDY_N         => pcie_trn.rx.src_rdy_n, -- 
      TRN_RDST_RDY_N         => pcie_trn.rx.dst_rdy_n, -- 
      TRN_RSOF_N             => pcie_trn.rx.sof_n,     -- Start of Frame
      TRN_REOF_N             => pcie_trn.rx.eof_n,     -- End of Frame
      TRN_RNP_OK_N           => pcie_trn.rx.np_ok_n,   -- Ready to accept Non-posted request
      TRN_RERRFWD_N          => pcie_trn.rx.err_fwd_n, -- Error forward
      TRN_RD                 => pcie_trn.rx.data,      -- Data
      TRN_RREM_N             => pcie_trn.rx.rem_n,     -- Data reminder
      TRN_RFC_PH_AV          => pcie_trn.rx.fc_ph_av,  -- Posted Header Flow Credits Available
      TRN_RFC_PD_AV          => pcie_trn.rx.fc_pd_av,  -- Posted Data Flow Credits Available
      TRN_RFC_NPH_AV         => pcie_trn.rx.fc_nph_av, -- Non-posted Header Flow Credits Available
      TRN_RFC_NPD_AV         => pcie_trn.rx.fc_npd_av, -- Non-posted Data Flow Credits Available
      TRN_RCPL_STREAMING_N   => '1',
      -- Transaction Transmit
      TRN_TSOF_N             => pcie_trn.tx.sof_n,
      TRN_TEOF_N             => pcie_trn.tx.eof_n,
      TRN_TSRC_RDY_N         => pcie_trn.tx.src_rdy_n,
      TRN_TDST_RDY_N         => pcie_trn.tx.dst_rdy_n,
      TRN_TD                 => pcie_trn.tx.data,      --
      TRN_TREM_N             => pcie_trn.tx.rem_n,     --
      TRN_TSRC_DSC_N         => pcie_trn.tx.src_dsc_n, -- TX source discontinue
      TRN_TDST_DSC_N         => pcie_trn.tx.dst_dcs_n, -- TX destination discontinue
      TRN_TBUF_AV            => pcie_trn.tx.buf_av,    -- TX buffers available
      TRN_TERRFWD_N          => '1',
      -- Endpoint configuration & status
      CFG_BUS_NUMBER         => pcie_cfg.bus_num,
      CFG_DEVICE_NUMBER      => pcie_cfg.device_num,
      CFG_FUNCTION_NUMBER    => pcie_cfg.func_num,
      CFG_PCIE_LINK_STATE_N  => open, -- PCIe link status
      CFG_STATUS             => open, -- PCIe status register output
      CFG_DSTATUS            => open, -- Device status register output
      CFG_COMMAND            => open, -- PCIe status register output   
      CFG_DCOMMAND( 7 downto 5) => pcie_cfg.max_payload_size, -- Device control (command) register output   
      CFG_DCOMMAND( 4 downto 0) => cfg_dcommand_4_0,
      CFG_DCOMMAND(15 downto 8) => cfg_dcommand_15_8,
      CFG_LSTATUS            => open, -- PCIe link status register output
      CFG_LCOMMAND           => open, -- PCIe link control (command) register out
      -- Error reporting
      CFG_TRN_PENDING_N      => '1', -- Set when a Mater transaction (read request) is pending
      CFG_ERR_CPL_TIMEOUT_N  => '1', -- Completition timeout
      CFG_ERR_UR_N           => '1', -- Error - unsupported reguest   
      CFG_ERR_COR_N          => '1', -- Correctable error
      CFG_ERR_POSTED_N       => '1', -- 
      CFG_ERR_TLP_CPL_HEADER => X"000000000000", -- TLP header of the error paket
      CFG_ERR_CPL_UNEXPECT_N => '1', -- Unexpected completition
      CFG_ERR_ECRC_N         => '1', -- ECRC error
      CFG_ERR_CPL_ABORT_N    => '1', -- Completition aborted
      -- Interrupts
      CFG_INTERRUPT_N        => '1',  -- Interrupt request
      CFG_INTERRUPT_RDY_N    => open, -- Interrupt grant
      -- Power management
      CFG_TO_TURNOFF_N       => open, -- Main power will be turned off
      CFG_PM_WAKE_N          => '1',  -- PME Wake request
      CFG_DSN                => X"0000000000000000", -- Device serial number
      -- Internal configuration space 
      CFG_WR_EN_N            => '1',          -- Write is not supported
      CFG_DI                 => X"00000000",  -- Write is not supported
      CFG_DO                 => open,         -- CFG space data output
      CFG_RD_EN_N            => '1',         -- CFG space read enable
      CFG_DWADDR             => "0000000000", -- CFG space address
      CFG_RD_WR_DONE_N       => open,         -- CFG read/write done
      CFG_BYTE_EN_N          => "1111",       -- Write BE - not supported
      -- PCI Express serial data interface
      PCI_EXP_TXN            => PCI_EXP_TXN,
      PCI_EXP_TXP            => PCI_EXP_TXP,
      PCI_EXP_RXN            => PCI_EXP_RXN,
      PCI_EXP_RXP            => PCI_EXP_RXP 
   );

   trn_reset <= not trn_reset_n;

   -- -------------------------------------------------------------------------
   --                       PCI Express to IB Bridge                         --
   -- -------------------------------------------------------------------------
   
   PCIE2IB_BRIDGE_U: entity work.PCIE2IB_BRIDGE
   generic map (
      IB_BASE_ADDR => IB_BASE_ADDR,  -- IB Base Address
      LTAG_WIDTH   => LTAG_WIDTH,    -- 'Local Read' Buffer tag width
      GTAG_WIDTH   => GTAG_WIDTH,    -- 'Global Read' Buffer tag width
      BAR_HIT_MASK => BAR_HIT_MASK,  -- Base Address Register hit mask for common transaction
      BAR0_BASE    => BAR0_BASE,
      BAR1_BASE    => BAR1_BASE,
      BAR2_BASE    => BAR2_BASE,
      BAR3_BASE    => BAR3_BASE,
      BAR4_BASE    => BAR4_BASE,
      BAR5_BASE    => BAR5_BASE,
      BAR6_BASE    => BAR6_BASE,
      BAR0_MASK    => BAR0_MASK,
      BAR1_MASK    => BAR1_MASK,
      BAR2_MASK    => BAR2_MASK,
      BAR3_MASK    => BAR3_MASK,
      BAR4_MASK    => BAR4_MASK,
      BAR5_MASK    => BAR5_MASK,
      BAR6_MASK    => BAR6_MASK
   )                
   port map (       
      -- Common Interface
      CLK              => trn_clk,
      RESET            => trn_reset,
      -- PCI Express Transaction Layer interface ------------------------------
      PCIE             => pcie_trn,
      -- Internal Bus interface -----------------------------------------------
      IB               => ib,
      -- Bus Master interface -------------------------------------------------
      BM               => bm,
      -- Configuration interface
      CFG              => pcie_cfg
   );
   
   IB_CLK <= trn_clk;
   IB_RST <= trn_reset;
   
end STRUCTURAL;



