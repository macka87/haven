-- combov2_pci.vhd : PCIe and Spartan interface for the ComboLXT card
-- Copyright (C) 2008 CESNET
-- Author(s): Stepan Friedl <friedl@liberouter.org>
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
-- TODO list :
--
-- --------------------------------------------------------------------
--                          Entity declaration
-- --------------------------------------------------------------------
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.ib_pkg.all;

-- ----------------------------------------------------------------------------
--                              Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of cv2_pci is

 -------------------------------------------------------------------
  --  ILA core component declaration
  -------------------------------------------------------------------
  component ila
    port
    (
      control     : in    std_logic_vector(35 downto 0);
      clk         : in    std_logic;
      trig0       : in    std_logic_vector(63 downto 0);
      trig1       : in    std_logic_vector(15 downto 0)
    );
  end component;
  
  component icon
    port
    (
      control0    :   out std_logic_vector(35 downto 0);
      control1    :   out std_logic_vector(35 downto 0)
    );
  end component;
  
  component icon3
    port
    (
      control0    :   out std_logic_vector(35 downto 0);
      control1    :   out std_logic_vector(35 downto 0);
      control2    :   out std_logic_vector(35 downto 0)
    );
  end component;

  signal control0 : std_logic_vector(35 downto 0);
  signal control1 : std_logic_vector(35 downto 0);
  signal control2 : std_logic_vector(35 downto 0);
  signal rx_trig0 : std_logic_vector(63 downto 0);
  signal rx_trig1 : std_logic_vector(15 downto 0);
  signal tx_trig0 : std_logic_vector(63 downto 0);
  signal tx_trig1 : std_logic_vector(15 downto 0);
  signal ib_trig0 : std_logic_vector(63 downto 0);
  signal ib_trig1 : std_logic_vector(15 downto 0);
  signal control  : std_logic_vector(35 downto 0);
  
  attribute noopt : boolean;
  attribute dont_touch : boolean;
 
  attribute noopt of icon  : component is TRUE;
  attribute noopt of icon3 : component is TRUE;
  attribute noopt of ila   : component is TRUE;
  attribute dont_touch of icon : component is TRUE;
  attribute dont_touch of icon3 : component is TRUE;
  attribute dont_touch of ila : component is TRUE;  


-- Xilinx LogiCORE PCI express block plus ------------------------------------
--    component endpoint_blk_plus_v1_5
--    port (
--       -- 
--       FAST_TRAIN_SIMULATION_ONLY : in std_logic;      
--       TWO_PLM_AUTO_CONFIG    : in  std_logic_vector( 1 downto 0);      
--       -- System interface
--       SYS_RESET_N            : in std_logic;
--       SYS_CLK                : in std_logic;
--       -- Transaction interface 
--       TRN_CLK                : out std_logic;
--       TRN_RESET_N            : out std_logic;
--       TRN_LNK_UP_N           : out std_logic;      
--       -- Receive --
--       TRN_RBAR_HIT_N         : out std_logic_vector( 6 downto 0); -- BAR hit
--       TRN_RSRC_RDY_N         : out std_logic; -- Source ready
--       TRN_RDST_RDY_N         : in  std_logic; -- Destination ready
--       TRN_RSOF_N             : out std_logic; -- Start of Frame
--       TRN_REOF_N             : out std_logic; -- End of Frame
--       TRN_RNP_OK_N           : in  std_logic; -- Ready to accept Non-posted request
--       TRN_RSRC_DSC_N         : out std_logic; -- Discontinue - packet abort
--       TRN_RERRFWD_N          : out std_logic; -- Error forward - packet bad
--       TRN_RD                 : out std_logic_vector(63 downto 0); -- Data
--       TRN_RREM_N             : out std_logic_vector( 7 downto 0); -- Data reminder
--       TRN_RFC_NPH_AV         : out std_logic_vector( 7 downto 0); -- Non-posted Header Flow Credits Available  
--       TRN_RFC_NPD_AV         : out std_logic_vector(11 downto 0); -- Non-posted Data Flow Credits Available
--       TRN_RFC_PH_AV          : out std_logic_vector( 7 downto 0); -- Posted Header Flow Credits Available
--       TRN_RFC_PD_AV          : out std_logic_vector(11 downto 0); -- Posted Data Flow Credits Available
--       TRN_RCPL_STREAMING_N   : in  std_logic;
--       -- Transmit --
--       TRN_TSOF_N             : in  std_logic; --        
--       TRN_TEOF_N             : in  std_logic; --
--       TRN_TSRC_RDY_N         : in  std_logic; --
--       TRN_TDST_RDY_N         : out std_logic; --            
--       TRN_TD                 : in  std_logic_vector(63 downto 0);      
--       TRN_TREM_N             : in  std_logic_vector( 7 downto 0);
--       TRN_TBUF_AV            : out std_logic_vector( 2 downto 0); -- Buffers available
--       TRN_TSRC_DSC_N         : in  std_logic; -- TX source discontinue
--       TRN_TDST_DSC_N         : out std_logic; -- TX destination discontinue
--       TRN_TERRFWD_N          : in  std_logic;      
--       -- Endpoint configuration
--       CFG_BUS_NUMBER         : out std_logic_vector( 7 downto 0);
--       CFG_DEVICE_NUMBER      : out std_logic_vector( 4 downto 0);
--       CFG_FUNCTION_NUMBER    : out std_logic_vector( 2 downto 0);      
--       -- 
--       CFG_TO_TURNOFF_N       : out std_logic;
--       CFG_ERR_POSTED_N       : in  std_logic;
--       CFG_TRN_PENDING_N      : in  std_logic;
--       CFG_ERR_CPL_TIMEOUT_N  : in  std_logic;
--       -- 
--       CFG_INTERRUPT_N        : in std_logic;
--       CFG_INTERRUPT_RDY_N    : out std_logic;
--       CFG_INTERRUPT_DI       : in std_logic_vector( 7 downto 0);
--       CFG_INTERRUPT_MMENABLE : out std_logic_vector( 2 downto 0);
--       CFG_INTERRUPT_MSIENABLE: out std_logic;
--       CFG_INTERRUPT_ASSERT_N : in std_logic;
--       CFG_INTERRUPT_DO       : out std_logic_vector( 7 downto 0);
--       --
--       CFG_ERR_UR_N           : in std_logic;
--       CFG_RD_EN_N            : in std_logic;
--       CFG_ERR_ECRC_N         : in std_logic;
--       CFG_ERR_CPL_ABORT_N    : in std_logic;
--       CFG_WR_EN_N            : in  std_logic;
--       CFG_RD_WR_DONE_N       : out std_logic;
--       CFG_ERR_COR_N          : in std_logic;
--       CFG_ERR_CPL_UNEXPECT_N : in std_logic;
--       CFG_PM_WAKE_N          : in std_logic;
--       CFG_BYTE_EN_N          : in  std_logic_vector( 3 downto 0);
--       CFG_ERR_TLP_CPL_HEADER : in  std_logic_vector(47 downto 0);
--       CFG_LCOMMAND           : out std_logic_vector(15 downto 0);
--       CFG_DSTATUS            : out std_logic_vector(15 downto 0);
--       CFG_DSN                : in  std_logic_vector(63 downto 0);
--       CFG_STATUS             : out std_logic_vector(15 downto 0);
--       CFG_COMMAND            : out std_logic_vector(15 downto 0);
--       CFG_DI                 : in  std_logic_vector(31 downto 0);
--       CFG_DO                 : out std_logic_vector(31 downto 0);
--       CFG_DWADDR             : in  std_logic_vector( 9 downto 0);
--       CFG_DCOMMAND           : out std_logic_vector(15 downto 0);
--       CFG_PCIE_LINK_STATE_N  : out std_logic_vector( 2 downto 0);
--       CFG_LSTATUS            : out std_logic_vector(15 downto 0);
--       -- PCI Express interface
--       PCI_EXP_TXN            : out std_logic_vector(7 downto 0);
--       PCI_EXP_TXP            : out std_logic_vector(7 downto 0);      
--       PCI_EXP_RXN            : in  std_logic_vector(7 downto 0);
--       PCI_EXP_RXP            : in  std_logic_vector(7 downto 0)
--    );
--    end component;

component endpoint_blk_plus_v1_9
	port (
	   PCI_EXP_TXP: OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
	   PCI_EXP_TXN: OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
	   PCI_EXP_RXP: IN STD_LOGIC_VECTOR(7 DOWNTO 0);
	   PCI_EXP_RXN: IN STD_LOGIC_VECTOR(7 DOWNTO 0);
	   TRN_CLK: OUT STD_LOGIC;
	   TRN_RESET_N: OUT STD_LOGIC;
	   TRN_LNK_UP_N: OUT STD_LOGIC;
	   TRN_TD: IN STD_LOGIC_VECTOR(63 DOWNTO 0);
	   TRN_TREM_N: IN STD_LOGIC_VECTOR(7 DOWNTO 0);
	   TRN_TSOF_N: IN STD_LOGIC;
	   TRN_TEOF_N: IN STD_LOGIC;
	   TRN_TSRC_RDY_N: IN STD_LOGIC;
	   TRN_TDST_RDY_N: OUT STD_LOGIC;
	   TRN_TDST_DSC_N: OUT STD_LOGIC;
	   TRN_TSRC_DSC_N: IN STD_LOGIC;
	   TRN_TERRFWD_N: IN STD_LOGIC;
	   TRN_TBUF_AV: OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
	   TRN_RD: OUT STD_LOGIC_VECTOR(63 DOWNTO 0);
	   TRN_RREM_N: OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
	   TRN_RSOF_N: OUT STD_LOGIC;
	   TRN_REOF_N: OUT STD_LOGIC;
	   TRN_RSRC_RDY_N: OUT STD_LOGIC;
	   TRN_RSRC_DSC_N: OUT STD_LOGIC;
	   TRN_RDST_RDY_N: IN STD_LOGIC;
	   TRN_RERRFWD_N: OUT STD_LOGIC;
	   TRN_RNP_OK_N: IN STD_LOGIC;
	   TRN_RBAR_HIT_N: OUT STD_LOGIC_VECTOR(6 DOWNTO 0);
	   TRN_RFC_NPH_AV: OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
	   TRN_RFC_NPD_AV: OUT STD_LOGIC_VECTOR(11 DOWNTO 0);
	   TRN_RFC_PH_AV: OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
	   TRN_RFC_PD_AV: OUT STD_LOGIC_VECTOR(11 DOWNTO 0);
	   TRN_RCPL_STREAMING_N: IN STD_LOGIC;
	   CFG_DO: OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
	   CFG_RD_WR_DONE_N: OUT STD_LOGIC;
	   CFG_DI: IN STD_LOGIC_VECTOR(31 DOWNTO 0);
	   CFG_BYTE_EN_N: IN STD_LOGIC_VECTOR(3 DOWNTO 0);
	   CFG_DWADDR: IN STD_LOGIC_VECTOR(9 DOWNTO 0);
	   CFG_WR_EN_N: IN STD_LOGIC;
	   CFG_RD_EN_N: IN STD_LOGIC;
	   CFG_ERR_COR_N: IN STD_LOGIC;
	   CFG_ERR_UR_N: IN STD_LOGIC;
	   CFG_ERR_ECRC_N: IN STD_LOGIC;
	   CFG_ERR_CPL_TIMEOUT_N: IN STD_LOGIC;
	   CFG_ERR_CPL_ABORT_N: IN STD_LOGIC;
	   CFG_ERR_CPL_UNEXPECT_N: IN STD_LOGIC;
	   CFG_ERR_POSTED_N: IN STD_LOGIC;
	   CFG_ERR_LOCKED_N: IN STD_LOGIC;
	   CFG_ERR_TLP_CPL_HEADER: IN STD_LOGIC_VECTOR(47 DOWNTO 0);
	   CFG_ERR_CPL_RDY_N: OUT STD_LOGIC;
	   CFG_INTERRUPT_N: IN STD_LOGIC;
	   CFG_INTERRUPT_RDY_N: OUT STD_LOGIC;
	   CFG_INTERRUPT_ASSERT_N: IN STD_LOGIC;
	   CFG_INTERRUPT_DI: IN STD_LOGIC_VECTOR(7 DOWNTO 0);
	   CFG_INTERRUPT_DO: OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
	   CFG_INTERRUPT_MMENABLE: OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
	   CFG_INTERRUPT_MSIENABLE: OUT STD_LOGIC;
	   CFG_TO_TURNOFF_N: OUT STD_LOGIC;
	   CFG_PM_WAKE_N: IN STD_LOGIC;
	   CFG_PCIE_LINK_STATE_N: OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
	   CFG_TRN_PENDING_N: IN STD_LOGIC;
	   CFG_BUS_NUMBER: OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
	   CFG_DEVICE_NUMBER: OUT STD_LOGIC_VECTOR(4 DOWNTO 0);
	   CFG_FUNCTION_NUMBER: OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
	   CFG_DSN: IN STD_LOGIC_VECTOR(63 DOWNTO 0);
	   CFG_STATUS: OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
	   CFG_COMMAND: OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
	   CFG_DSTATUS: OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
	   CFG_DCOMMAND: OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
	   CFG_LSTATUS: OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
	   CFG_LCOMMAND: OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
	   FAST_TRAIN_SIMULATION_ONLY: IN STD_LOGIC;
	   SYS_CLK: IN STD_LOGIC;
	   REFCLKOUT: OUT STD_LOGIC;
	   SYS_RESET_N: IN STD_LOGIC
   );
end component;
 
   -- ------------------ Signals declaration ----------------------------------
   -- Clocks & resets
   signal regiob_sp3_reset_n     : std_logic;
   signal reset_i          : std_logic;
   signal reset_sync       : std_logic;
   -- ICS
      -- Bridge <-> Switch
   signal ibus0_down_data        : std_logic_vector(63 downto 0);
   signal ibus0_down_sop_n       : std_logic;
   signal ibus0_down_eop_n       : std_logic;
   signal ibus0_down_src_rdy_n   : std_logic;
   signal ibus0_down_dst_rdy_n   : std_logic;
   signal ibus0_up_data          : std_logic_vector(63 downto 0);
   signal ibus0_up_sop_n         : std_logic;
   signal ibus0_up_eop_n         : std_logic;
   signal ibus0_up_src_rdy_n     : std_logic;
   signal ibus0_up_dst_rdy_n     : std_logic;

      -- Switch <-> Spartan
   signal ibus_bar0_down_data      : std_logic_vector(63 downto 0);
   signal ibus_bar0_down_sop_n     : std_logic;
   signal ibus_bar0_down_eop_n     : std_logic;
   signal ibus_bar0_down_src_rdy_n : std_logic;
   signal ibus_bar0_down_dst_rdy_n : std_logic;
   signal ibus_bar0_up_data        : std_logic_vector(63 downto 0);
   signal ibus_bar0_up_sop_n       : std_logic;
   signal ibus_bar0_up_eop_n       : std_logic;
   signal ibus_bar0_up_src_rdy_n   : std_logic;
   signal ibus_bar0_up_dst_rdy_n   : std_logic;
      
      -- Switch <-> IB_ASYNC
   signal async_down_data        : std_logic_vector(63 downto 0);
   signal async_down_sop_n       : std_logic;
   signal async_down_eop_n       : std_logic;
   signal async_down_src_rdy_n   : std_logic;
   signal async_down_dst_rdy_n   : std_logic;
   signal async_up_data          : std_logic_vector(63 downto 0);
   signal async_up_sop_n         : std_logic;
   signal async_up_eop_n         : std_logic;
   signal async_up_src_rdy_n     : std_logic;
   signal async_up_dst_rdy_n     : std_logic;

      -- Switch <-> User
   signal user_down_data        : std_logic_vector(63 downto 0);
   signal user_down_sop_n       : std_logic;
   signal user_down_eop_n       : std_logic;
   signal user_down_src_rdy_n   : std_logic;
   signal user_down_dst_rdy_n   : std_logic;
   signal user_up_data          : std_logic_vector(63 downto 0);
   signal user_up_sop_n         : std_logic;
   signal user_up_eop_n         : std_logic;
   signal user_up_src_rdy_n     : std_logic;
   signal user_up_dst_rdy_n     : std_logic;

   signal bar0_wr          : t_ibmi_write64;
   signal bar0_rd          : t_ibmi_read64s;
   -- PCI-E transaction interface (TRN)
   signal trn_clk     : std_logic; -- Clock
   signal trn_reset_n : std_logic; -- #Reset
   signal trn_lnk_up_n: std_logic; -- Link up
   signal trn_reset   : std_logic; -- Reset

   attribute buffer_type:string;
   attribute buffer_type of trn_clk:signal is "none";
    
   signal trn_rsof_n      : std_logic;                      -- signals the start of a packet
   signal trn_reof_n      : std_logic;                      -- signals the end of a packet
   signal trn_rdata       : std_logic_vector(63 downto 0);  -- packet data to be transmitted
   signal trn_rrem_n      : std_logic_vector( 7 downto 0);  -- packet data validity (legal values: 00000000/00001111)
   signal trn_rsrc_rdy_n  : std_logic;                      -- source ready
   signal trn_rdst_rdy_n  : std_logic;                      -- destination ready 
   signal trn_rsrc_dsc_n  : std_logic;                      -- source discontinue, asserted when the physical link is going into reset.
   signal trn_rerr_fwd_n  : std_logic;                      -- error forward, marks the packet in progress as error poisoned
   signal trn_rnp_ok_n    : std_logic;                      -- Non-Posted OK, ready to accept a Non-Posted Request packet
   signal trn_rbar_hit_n  : std_logic_vector( 6 downto 0);  -- Indicates BAR(s) targeted by the current receive transaction      
   signal trn_rfc_ph_av   : std_logic_vector( 7 downto 0);  -- The number of Posted Header FC credits available to the remote link partner.
   signal trn_rfc_pd_av   : std_logic_vector(11 downto 0);  -- The number of Posted Data FC credits available to the remote link partner
   signal trn_rfc_nph_av  : std_logic_vector( 7 downto 0);  -- Number of Non-Posted Header FC credits available to the remote link partner
   signal trn_rfc_npd_av  : std_logic_vector(11 downto 0);  -- Number of Non-Posted Data FC credits available to the remote link partner
   signal trn_rcpl_streaming_n : std_logic;

   signal trn_tsof_n           : std_logic;                      -- signals the start of a packet
   signal trn_teof_n           : std_logic;                      -- signals the end of a packet
   signal trn_tdata            : std_logic_vector(63 downto 0);  -- packet data to be transmitted
   signal trn_trem_n           : std_logic_vector( 7 downto 0);  -- packet data validity (legal values: 00000000/00001111)
   signal trn_tsrc_rdy_n       : std_logic;                      -- source ready
   signal trn_tdst_rdy_n       : std_logic;                      -- destination ready 
   signal trn_tsrc_dsc_n       : std_logic;                      -- source discontinue, may be asserted any time starting on the first cycle after SOF to EOF, inclusive
   signal trn_terrfwd_n        : std_logic;
   signal trn_tdst_dcs_n       : std_logic;                      -- destination discontinue: Asserted when the physical link is going into reset.
   signal trn_tbuf_av          : std_logic_vector( 3 downto 0);  -- Indicates transmit buffer availability in the core (0:Non-Posted,1:Posted,2:Completion)
     
   -- PCI-E configuration   
   signal cfg_bus_number         : std_logic_vector( 7 downto 0);
   signal cfg_device_number      : std_logic_vector( 4 downto 0);
   signal cfg_function_number    : std_logic_vector( 2 downto 0);
   signal cfg_to_turnoff_n       : std_logic;
   signal cfg_err_posted_n       : std_logic;
   signal cfg_trn_pending_n      : std_logic;
   signal cfg_err_cpl_timeout_n  : std_logic;
   signal cfg_interrupt_n        : std_logic;
   signal cfg_interrupt_rdy_n    : std_logic;
   signal cfg_interrupt_assert_n : std_logic;
   signal cfg_interrupt_di       : std_logic_vector(7 downto 0);
   signal cfg_interrupt_do       : std_logic_vector(7 downto 0);
   signal cfg_interrupt_mmenable : std_logic_vector(2 downto 0);
   signal cfg_interrupt_msienable: std_logic;
   signal cfg_err_ur_n           : std_logic;
   signal cfg_rd_en_n            : std_logic;
   signal cfg_err_ecrc_n         : std_logic;
   signal cfg_err_cpl_abort_n    : std_logic;
   signal cfg_wr_en_n            : std_logic;
   signal cfg_rd_wr_done_n       : std_logic;
   signal cfg_err_cor_n          : std_logic;
   signal cfg_err_cpl_unexpect_n : std_logic;
   signal cfg_pm_wake_n          : std_logic;
   signal cfg_byte_en_n          : std_logic_vector( 3 downto 0);
   signal cfg_err_tlp_cpl_header : std_logic_vector(47 downto 0);
   signal cfg_lcommand           : std_logic_vector(15 downto 0);
   signal cfg_dstatus            : std_logic_vector(15 downto 0);
   signal cfg_dsn                : std_logic_vector(63 downto 0);
   signal cfg_status             : std_logic_vector(15 downto 0);
   signal cfg_command            : std_logic_vector(15 downto 0);
   signal cfg_di                 : std_logic_vector(31 downto 0);
   signal cfg_do                 : std_logic_vector(31 downto 0);
   signal cfg_dwaddr             : std_logic_vector( 9 downto 0);
   signal cfg_dcommand           : std_logic_vector(15 downto 0);
   signal cfg_pcie_link_state_n  : std_logic_vector( 2 downto 0);
   signal cfg_lstatus            : std_logic_vector(15 downto 0); 

   -- new in v1.9
  signal cfg_err_locked_n        : std_logic;
  signal cfg_err_cpl_rdy_n       : std_logic;  
  signal pcie_refclkout          : std_logic;

begin

   -- -------------------------------------------------------------------------
   --                         PCIE to IB TOP LEVEL                           --
   -- ------------------------------------------------------------------------- 

--    PCIE_BLK_PLUS_I: endpoint_blk_plus_v1_5
--    port map (
--       -- 
--       FAST_TRAIN_SIMULATION_ONLY => '0',                                              
--       TWO_PLM_AUTO_CONFIG    => "00",
--       -- System interface
--       SYS_RESET_N            => PCIE_RST_N,  -- System reset (cold, hot), active low
--       SYS_CLK                => PCIE_CLK,    -- Reference clock, 100 or 250MHz
--       -- Transaction interface
--       TRN_CLK                => trn_clk,     -- out
--       TRN_RESET_N            => trn_reset_n, -- out - (sys_rst OR NOT pll_lock OR gtp_lock_lost OR NOT dl_active_state)
--       TRN_LNK_UP_N           => trn_lnk_up_n,   -- out
--       -- Transaction Receive 
--       TRN_RBAR_HIT_N         => trn_rbar_hit_n, -- BAR hit
--       TRN_RSRC_DSC_N         => trn_rsrc_dsc_n, -- Discontinue - packet abort 
--       TRN_RSRC_RDY_N         => trn_rsrc_rdy_n, -- 
--       TRN_RDST_RDY_N         => trn_rdst_rdy_n, -- 
--       TRN_RSOF_N             => trn_rsof_n,     -- Start of Frame
--       TRN_REOF_N             => trn_reof_n,     -- End of Frame
--       TRN_RNP_OK_N           => trn_rnp_ok_n,   -- Ready to accept Non-posted request
--       TRN_RERRFWD_N          => trn_rerr_fwd_n, -- Error forward
--       TRN_RD                 => trn_rdata,      -- Data
--       TRN_RREM_N             => trn_rrem_n,     -- Data reminder
--       TRN_RFC_PH_AV          => trn_rfc_ph_av,  -- Posted Header Flow Credits Available
--       TRN_RFC_PD_AV          => trn_rfc_pd_av,  -- Posted Data Flow Credits Available
--       TRN_RFC_NPH_AV         => trn_rfc_nph_av, -- Non-posted Header Flow Credits Available
--       TRN_RFC_NPD_AV         => trn_rfc_npd_av, -- Non-posted Data Flow Credits Available
--       TRN_RCPL_STREAMING_N   => trn_rcpl_streaming_n,
--       -- Transaction Transmit
--       TRN_TSOF_N             => trn_tsof_n,
--       TRN_TEOF_N             => trn_teof_n,
--       TRN_TSRC_RDY_N         => trn_tsrc_rdy_n,
--       TRN_TDST_RDY_N         => trn_tdst_rdy_n,
--       TRN_TD                 => trn_tdata,      --
--       TRN_TREM_N             => trn_trem_n,     --
--       TRN_TSRC_DSC_N         => trn_tsrc_dsc_n, -- TX source discontinue
--       TRN_TDST_DSC_N         => trn_tdst_dcs_n, -- TX destination discontinue
--       TRN_TBUF_AV            => trn_tbuf_av,    -- TX buffers available
--       TRN_TERRFWD_N          => trn_terrfwd_n,
--       -- Endpoint configuration & status
--       CFG_BUS_NUMBER         => cfg_bus_number,
--       CFG_DEVICE_NUMBER      => cfg_device_number,
--       CFG_FUNCTION_NUMBER    => cfg_function_number,
--       CFG_PCIE_LINK_STATE_N  => cfg_pcie_link_state_n, -- PCIe link status
--       CFG_STATUS             => cfg_status,   -- PCIe status register output
--       CFG_DSTATUS            => cfg_dstatus,  -- Device status register output
--       CFG_COMMAND            => cfg_command,  -- PCIe status register output   
--       CFG_DCOMMAND           => cfg_dcommand, -- Device control (command) register output   
--       CFG_LSTATUS            => cfg_lstatus,  -- PCIe link status register output
--       CFG_LCOMMAND           => cfg_lcommand, -- PCIe link control (command) register out
--       -- Error reporting
--       CFG_TRN_PENDING_N      => cfg_trn_pending_n,      -- Set when a Mater transaction (read request) is pending
--       CFG_ERR_CPL_TIMEOUT_N  => cfg_err_cpl_timeout_n,  -- Completition timeout
--       CFG_ERR_UR_N           => cfg_err_ur_n,           -- Error - unsupported reguest   
--       CFG_ERR_COR_N          => cfg_err_cor_n,          -- Correctable error
--       CFG_ERR_POSTED_N       => cfg_err_posted_n,       -- 
--       CFG_ERR_TLP_CPL_HEADER => cfg_err_tlp_cpl_header, -- TLP header of the error paket
--       CFG_ERR_CPL_UNEXPECT_N => cfg_err_cpl_unexpect_n, -- Unexpected completition
--       CFG_ERR_ECRC_N         => cfg_err_ecrc_n,         -- ECRC error
--       CFG_ERR_CPL_ABORT_N    => cfg_err_cpl_abort_n,    -- Completition aborted
--       -- Interrupts
--       CFG_INTERRUPT_N        => cfg_interrupt_n,     -- Interrupt request
--       CFG_INTERRUPT_ASSERT_N => cfg_interrupt_assert_n,
--       CFG_INTERRUPT_RDY_N    => cfg_interrupt_rdy_n, -- Interrupt grant
--       CFG_INTERRUPT_DI       => cfg_interrupt_di,
--       CFG_INTERRUPT_MMENABLE => cfg_interrupt_mmenable,
--       CFG_INTERRUPT_MSIENABLE=> cfg_interrupt_msienable,
--       CFG_INTERRUPT_DO       => cfg_interrupt_do,
--       -- Power management
--       CFG_TO_TURNOFF_N       => cfg_to_turnoff_n, -- Main power will be turned off
--       CFG_PM_WAKE_N          => cfg_pm_wake_n,    -- PME Wake request
--       CFG_DSN                => cfg_dsn,          -- Device serial number
--       -- Internal configuration space 
--       CFG_WR_EN_N            => cfg_wr_en_n,      -- Write is not supported
--       CFG_DI                 => cfg_di,           -- Write is not supported
--       CFG_DO                 => cfg_do,           -- CFG space data output
--       CFG_RD_EN_N            => cfg_rd_en_n,      -- CFG space read enable
--       CFG_DWADDR             => cfg_dwaddr,       -- CFG space address
--       CFG_RD_WR_DONE_N       => cfg_rd_wr_done_n, -- CFG read/write done
--       CFG_BYTE_EN_N          => cfg_byte_en_n,    -- Write BE - not supported
--       -- PCI Express serial data interface
--       PCI_EXP_TXN            => PCI_EXP_TXN,
--       PCI_EXP_TXP            => PCI_EXP_TXP,
--       PCI_EXP_RXN            => PCI_EXP_RXN,
--       PCI_EXP_RXP            => PCI_EXP_RXP 
--    );
     
   cfg_err_locked_n  <= '1';
   --cfg_err_cpl_rdy_n <= open;
   --pcie_refclkout    <= open;

   PCIE_BLK_PLUS_I: endpoint_blk_plus_v1_9
   port map (
      -- 
      FAST_TRAIN_SIMULATION_ONLY => '0',                                              
      -- TWO_PLM_AUTO_CONFIG    => "00",
      -- System interface
      SYS_RESET_N            => PCIE_RST_N,  -- System reset (cold, hot), active low
      SYS_CLK                => PCIE_CLK,    -- Reference clock, 100 or 250MHz
      REFCLKOUT              => pcie_refclkout, -- v1.9
      -- Transaction interface
      TRN_CLK                => trn_clk,     -- out
      TRN_RESET_N            => trn_reset_n, -- out - (sys_rst OR NOT pll_lock OR gtp_lock_lost OR NOT dl_active_state)
      TRN_LNK_UP_N           => trn_lnk_up_n,   -- out
      -- Transaction Receive 
      TRN_RBAR_HIT_N         => trn_rbar_hit_n, -- BAR hit
      TRN_RSRC_DSC_N         => trn_rsrc_dsc_n, -- Discontinue - packet abort 
      TRN_RSRC_RDY_N         => trn_rsrc_rdy_n, -- 
      TRN_RDST_RDY_N         => trn_rdst_rdy_n, -- 
      TRN_RSOF_N             => trn_rsof_n,     -- Start of Frame
      TRN_REOF_N             => trn_reof_n,     -- End of Frame
      TRN_RNP_OK_N           => trn_rnp_ok_n,   -- Ready to accept Non-posted request
      TRN_RERRFWD_N          => trn_rerr_fwd_n, -- Error forward
      TRN_RD                 => trn_rdata,      -- Data
      TRN_RREM_N             => trn_rrem_n,     -- Data reminder
      TRN_RFC_PH_AV          => trn_rfc_ph_av,  -- Posted Header Flow Credits Available
      TRN_RFC_PD_AV          => trn_rfc_pd_av,  -- Posted Data Flow Credits Available
      TRN_RFC_NPH_AV         => trn_rfc_nph_av, -- Non-posted Header Flow Credits Available
      TRN_RFC_NPD_AV         => trn_rfc_npd_av, -- Non-posted Data Flow Credits Available
      TRN_RCPL_STREAMING_N   => trn_rcpl_streaming_n,
      -- Transaction Transmit
      TRN_TSOF_N             => trn_tsof_n,
      TRN_TEOF_N             => trn_teof_n,
      TRN_TSRC_RDY_N         => trn_tsrc_rdy_n,
      TRN_TDST_RDY_N         => trn_tdst_rdy_n,
      TRN_TD                 => trn_tdata,      --
      TRN_TREM_N             => trn_trem_n,     --
      TRN_TSRC_DSC_N         => trn_tsrc_dsc_n, -- TX source discontinue
      TRN_TDST_DSC_N         => trn_tdst_dcs_n, -- TX destination discontinue
      TRN_TBUF_AV            => trn_tbuf_av,    -- TX buffers available
      TRN_TERRFWD_N          => trn_terrfwd_n,
      -- Endpoint configuration & status
      CFG_BUS_NUMBER         => cfg_bus_number,
      CFG_DEVICE_NUMBER      => cfg_device_number,
      CFG_FUNCTION_NUMBER    => cfg_function_number,
      CFG_PCIE_LINK_STATE_N  => cfg_pcie_link_state_n, -- PCIe link status
      CFG_STATUS             => cfg_status,   -- PCIe status register output
      CFG_DSTATUS            => cfg_dstatus,  -- Device status register output
      CFG_COMMAND            => cfg_command,  -- PCIe status register output   
      CFG_DCOMMAND           => cfg_dcommand, -- Device control (command) register output   
      CFG_LSTATUS            => cfg_lstatus,  -- PCIe link status register output
      CFG_LCOMMAND           => cfg_lcommand, -- PCIe link control (command) register out
      -- Error reporting
      CFG_TRN_PENDING_N      => cfg_trn_pending_n,      -- Set when a Mater transaction (read request) is pending
      CFG_ERR_CPL_TIMEOUT_N  => cfg_err_cpl_timeout_n,  -- Completition timeout
      CFG_ERR_UR_N           => cfg_err_ur_n,           -- Error - unsupported reguest   
      CFG_ERR_COR_N          => cfg_err_cor_n,          -- Correctable error
      CFG_ERR_POSTED_N       => cfg_err_posted_n,       -- 
      CFG_ERR_TLP_CPL_HEADER => cfg_err_tlp_cpl_header, -- TLP header of the error paket
      CFG_ERR_CPL_UNEXPECT_N => cfg_err_cpl_unexpect_n, -- Unexpected completition
      CFG_ERR_ECRC_N         => cfg_err_ecrc_n,         -- ECRC error
      CFG_ERR_CPL_ABORT_N    => cfg_err_cpl_abort_n,    -- Completition aborted
      CFG_ERR_LOCKED_N       => cfg_err_locked_n,       -- in v1.9
      CFG_ERR_CPL_RDY_N      => cfg_err_cpl_rdy_n,      -- in v1.9    
      -- Interrupts
      CFG_INTERRUPT_N        => cfg_interrupt_n,     -- Interrupt request
      CFG_INTERRUPT_ASSERT_N => cfg_interrupt_assert_n,
      CFG_INTERRUPT_RDY_N    => cfg_interrupt_rdy_n, -- Interrupt grant
      CFG_INTERRUPT_DI       => cfg_interrupt_di,
      CFG_INTERRUPT_MMENABLE => cfg_interrupt_mmenable,
      CFG_INTERRUPT_MSIENABLE=> cfg_interrupt_msienable,
      CFG_INTERRUPT_DO       => cfg_interrupt_do,
      -- Power management
      CFG_TO_TURNOFF_N       => cfg_to_turnoff_n, -- Main power will be turned off
      CFG_PM_WAKE_N          => cfg_pm_wake_n,    -- PME Wake request
      CFG_DSN                => cfg_dsn,          -- Device serial number
      -- Internal configuration space 
      CFG_WR_EN_N            => cfg_wr_en_n,      -- Write is not supported
      CFG_DI                 => cfg_di,           -- Write is not supported
      CFG_DO                 => cfg_do,           -- CFG space data output
      CFG_RD_EN_N            => cfg_rd_en_n,      -- CFG space read enable
      CFG_DWADDR             => cfg_dwaddr,       -- CFG space address
      CFG_RD_WR_DONE_N       => cfg_rd_wr_done_n, -- CFG read/write done
      CFG_BYTE_EN_N          => cfg_byte_en_n,    -- Write BE - not supported
      -- PCI Express serial data interface
      PCI_EXP_TXN            => PCI_EXP_TXN,
      PCI_EXP_TXP            => PCI_EXP_TXP,
      PCI_EXP_RXN            => PCI_EXP_RXN,
      PCI_EXP_RXP            => PCI_EXP_RXP 
   );
 
   PCIE_BRIDGE: entity work.PCIE2IB_BRIDGE 
   generic map (
      ENABLE_ALIGN_UNIT => false,
      BRIDGE_BASE_ADDR  => X"F0000000",
      -- BAR base addresses
      BAR0_REMAP        => X"C0000000",
      BAR1_REMAP        => X"C0000000",
      BAR2_REMAP        => X"00000000",
      BAR3_REMAP        => X"00000000",
      BAR4_REMAP        => X"C0010000", -- BAR4 = CPLD space -- remapped to ibus_bar0
      BAR5_REMAP        => X"C0000000",
      EXP_ROM_REMAP     => X"C0020000",
      -- BAR base addresses masks
      BAR0_MASK         => X"000FFFFF",
      BAR1_MASK         => X"000FFFFF",
      BAR2_MASK         => X"03FFFFFF",
      BAR3_MASK         => X"03FFFFFF",
      BAR4_MASK         => X"03FFFFFF",
      BAR5_MASK         => X"03FFFFFF",
      EXP_ROM_MASK      => X"000FFFFF"
   )
   port map (
       -- ----------- PCI Express Common Interface ------------------------------  
      trn_clk                 => trn_clk,
      trn_reset_n             => trn_reset_n,
       -- ----------- PCI Express TLP RX Interface ------------------------------
      trn_rd                  => trn_rdata,
      trn_rrem_n              => trn_rrem_n,
      trn_rsof_n              => trn_rsof_n,
      trn_reof_n              => trn_reof_n,
      trn_rsrc_rdy_n          => trn_rsrc_rdy_n,
      trn_rsrc_dsc_n          => trn_rsrc_dsc_n,
      trn_rdst_rdy_n          => trn_rdst_rdy_n,
      trn_rerrfwd_n           => trn_rerr_fwd_n,
      trn_rnp_ok_n            => trn_rnp_ok_n,
      trn_rbar_hit_n          => trn_rbar_hit_n,
      trn_rfc_nph_av          => trn_rfc_nph_av,
      trn_rfc_npd_av          => trn_rfc_npd_av,
      trn_rfc_ph_av           => trn_rfc_ph_av,
      trn_rfc_pd_av           => trn_rfc_pd_av,
      trn_rcpl_streaming_n    => trn_rcpl_streaming_n,
      -- ----------- PCI Express TLP TX Interface ------------------------------
      trn_lnk_up_n            => trn_lnk_up_n,
      trn_td                  => trn_tdata,     
      trn_trem_n              => trn_trem_n,    
      trn_tsof_n              => trn_tsof_n,    
      trn_teof_n              => trn_teof_n,
      trn_tsrc_rdy_n          => trn_tsrc_rdy_n,
      trn_tdst_rdy_n          => trn_tdst_rdy_n,
      trn_tsrc_dsc_n          => trn_tsrc_dsc_n,
      trn_terrfwd_n           => trn_terrfwd_n,
      trn_tdst_dsc_n          => trn_tdst_dcs_n,
      trn_tbuf_av             => trn_tbuf_av,
      -- ----------- PCI Express Host Configuration interface ------------------
      cfg_do                  => cfg_do,
      cfg_rd_wr_done_n        => cfg_rd_wr_done_n,
      cfg_di                  => cfg_di,
      cfg_dwaddr              => cfg_dwaddr,
      cfg_wr_en_n             => cfg_wr_en_n,
      cfg_rd_en_n             => cfg_rd_en_n,
      
      cfg_interrupt_n         => open, -- cfg_interrupt_n,
      cfg_interrupt_rdy_n     => cfg_interrupt_rdy_n,
      cfg_interrupt_mmenable  => cfg_interrupt_mmenable,
      cfg_interrupt_msienable => cfg_interrupt_msienable,
      cfg_interrupt_di        => open, -- cfg_interrupt_di,
      cfg_interrupt_do        => cfg_interrupt_do,
      cfg_interrupt_assert_n  => open, -- cfg_interrupt_assert_n,
      cfg_to_turnoff_n        => cfg_to_turnoff_n,
      cfg_byte_en_n           => cfg_byte_en_n,
      cfg_bus_number          => cfg_bus_number,
      cfg_device_number       => cfg_device_number,
      cfg_function_number     => cfg_function_number,
      cfg_status              => cfg_status,
      cfg_command             => cfg_command, 
      cfg_dstatus             => cfg_dstatus,
      cfg_dcommand            => cfg_dcommand,
      cfg_lstatus             => cfg_lstatus,
      cfg_lcommand            => cfg_lcommand,
      cfg_pm_wake_n           => cfg_pm_wake_n,
      cfg_pcie_link_state_n   => cfg_pcie_link_state_n,
      cfg_trn_pending_n       => cfg_trn_pending_n,
      cfg_dsn                 => cfg_dsn,
      --
      cfg_err_ecrc_n          => cfg_err_ecrc_n,
      cfg_err_ur_n            => cfg_err_ur_n,
      cfg_err_cpl_timeout_n   => cfg_err_cpl_timeout_n,
      cfg_err_cpl_unexpect_n  => cfg_err_cpl_unexpect_n,
      cfg_err_cpl_abort_n     => cfg_err_cpl_abort_n,
      cfg_err_posted_n        => cfg_err_posted_n,
      cfg_err_cor_n           => cfg_err_cor_n,
      cfg_err_tlp_cpl_header  => cfg_err_tlp_cpl_header,
      cfg_err_cpl_rdy_n       => '0',
      -- ----------- Internal Bus TX interface ---------------------------------
      TX_DATA                 => ibus0_down_data,
      TX_SOP_N                => ibus0_down_sop_n,
      TX_EOP_N                => ibus0_down_eop_n,
      TX_SRC_RDY_N            => ibus0_down_src_rdy_n,
      TX_DST_RDY_N            => ibus0_down_dst_rdy_n,
      -- ----------- Internal Bus RX interface ---------------------------------
      RX_DATA                 => ibus0_up_data,
      RX_SOP_N                => ibus0_up_sop_n,
      RX_EOP_N                => ibus0_up_eop_n,
      RX_SRC_RDY_N            => ibus0_up_src_rdy_n,
      RX_DST_RDY_N            => ibus0_up_dst_rdy_n
   );
   
   trn_reset <= not trn_reset_n;
          
   IB_SWITCH_BAR: entity work.IB_SWITCH_CORE
   generic map (
      -- Data Width (64/128)
      DATA_WIDTH        => 64,
      -- Port 0 Address Space 
      SWITCH_BASE       => X"00000000",
      SWITCH_LIMIT      => X"EFFFFFFF",
      -- Port 1 Address Space
      DOWNSTREAM0_BASE  => X"00000000", -- Application address space (BAR1)
      DOWNSTREAM0_LIMIT => X"BFFFFFFF",
      -- Port 2 Address Space
      DOWNSTREAM1_BASE  => X"C0000000", -- PCI bridge space (BAR0)
      DOWNSTREAM1_LIMIT => X"2FFFFFFF"
   )
   port map(
      -- Common Interface
      IB_CLK        => trn_clk,
      IB_RESET      => trn_reset,
      -- Upstream Port
      PORT0_DOWN_DATA      => ibus0_down_data,
      PORT0_DOWN_SOP_N     => ibus0_down_sop_n,
      PORT0_DOWN_EOP_N     => ibus0_down_eop_n,
      PORT0_DOWN_SRC_RDY_N => ibus0_down_src_rdy_n,
      PORT0_DOWN_DST_RDY_N => ibus0_down_dst_rdy_n,
      PORT0_UP_DATA        => ibus0_up_data,
      PORT0_UP_SOP_N       => ibus0_up_sop_n,
      PORT0_UP_EOP_N       => ibus0_up_eop_n,
      PORT0_UP_SRC_RDY_N   => ibus0_up_src_rdy_n,
      PORT0_UP_DST_RDY_N   => ibus0_up_dst_rdy_n,
      -- Downstream Ports
         -- To IB_ASYNC or directly to user
      PORT1_DOWN_DATA      => async_down_data,     
      PORT1_DOWN_SOP_N     => async_down_sop_n,    
      PORT1_DOWN_EOP_N     => async_down_eop_n,    
      PORT1_DOWN_SRC_RDY_N => async_down_src_rdy_n,
      PORT1_DOWN_DST_RDY_N => async_down_dst_rdy_n,
      PORT1_UP_DATA        => async_up_data,     
      PORT1_UP_SOP_N       => async_up_sop_n,    
      PORT1_UP_EOP_N       => async_up_eop_n,    
      PORT1_UP_SRC_RDY_N   => async_up_src_rdy_n,
      PORT1_UP_DST_RDY_N   => async_up_dst_rdy_n,
         -- To Spartan
      PORT2_DOWN_DATA      => ibus_bar0_down_data,     
      PORT2_DOWN_SOP_N     => ibus_bar0_down_sop_n,    
      PORT2_DOWN_EOP_N     => ibus_bar0_down_eop_n,    
      PORT2_DOWN_SRC_RDY_N => ibus_bar0_down_src_rdy_n,
      PORT2_DOWN_DST_RDY_N => ibus_bar0_down_dst_rdy_n,
      PORT2_UP_DATA        => ibus_bar0_up_data,     
      PORT2_UP_SOP_N       => ibus_bar0_up_sop_n,    
      PORT2_UP_EOP_N       => ibus_bar0_up_eop_n,    
      PORT2_UP_SRC_RDY_N   => ibus_bar0_up_src_rdy_n,
      PORT2_UP_DST_RDY_N   => ibus_bar0_up_dst_rdy_n
   ); 
   
   BRIDGE_RST <= trn_reset;
   BRIDGE_CLK <= trn_clk;

   -- Use async FIFOs to connect IB
   use_async_gen : if USE_IB_ASYNC generate
      IB_ASYNC_DOWN_I : entity work.ib_asfifo_64b
      port map(
         RX_CLK      => trn_clk,
         RX_RESET    => trn_reset,
         TX_CLK      => IB_CLK,
         TX_RESET    => IB_RST,

         RX_DATA     => async_down_data,
         RX_EOP_N    => async_down_eop_n,
         RX_SOP_N    => async_down_sop_n,
         RX_SRC_RDY_N=> async_down_src_rdy_n,
         RX_DST_RDY_N=> async_down_dst_rdy_n,
         TX_DATA     => user_DOWN_DATA,
         TX_EOP_N    => user_DOWN_EOP_N,
         TX_SOP_N    => user_DOWN_SOP_N,
         TX_SRC_RDY_N=> user_DOWN_SRC_RDY_N,
         TX_DST_RDY_N=> user_DOWN_DST_RDY_N
      );
      IB_ASYNC_UP_I : entity work.ib_asfifo_64b
      port map(
         RX_CLK      => IB_CLK,
         RX_RESET    => IB_RST,
         TX_CLK      => trn_clk,
         TX_RESET    => trn_reset,

         RX_DATA     => user_UP_DATA,
         RX_EOP_N    => user_UP_EOP_N,
         RX_SOP_N    => user_UP_SOP_N,
         RX_SRC_RDY_N=> user_UP_SRC_RDY_N,
         RX_DST_RDY_N=> user_UP_DST_RDY_N,
         TX_DATA     => async_up_data,
         TX_EOP_N    => async_up_eop_n,
         TX_SOP_N    => async_up_sop_n,
         TX_SRC_RDY_N=> async_up_src_rdy_n,
         TX_DST_RDY_N=> async_up_dst_rdy_n
      );

      user_up_data      <= IB_UP_DATA;
      user_up_sop_n     <= IB_UP_SOP_N;
      user_up_eop_n     <= IB_UP_EOP_N;
      user_up_src_rdy_n <= IB_UP_SRC_RDY_N;
      IB_UP_DST_RDY_N   <= user_up_dst_rdy_n;

      IB_DOWN_DATA         <= user_down_data;
      IB_DOWN_SOP_N        <= user_down_sop_n;
      IB_DOWN_EOP_N        <= user_down_eop_n;
      IB_DOWN_SRC_RDY_N    <= user_down_src_rdy_n;
      user_down_dst_rdy_n  <= IB_DOWN_DST_RDY_N;

   end generate;


   no_use_async_gen : if not USE_IB_ASYNC generate
      IB_DOWN_DATA      <= async_down_data;
      IB_DOWN_SOP_N     <= async_down_sop_n;
      IB_DOWN_EOP_N     <= async_down_eop_n;
      IB_DOWN_SRC_RDY_N <= async_down_src_rdy_n;
      async_down_dst_rdy_n <= IB_DOWN_DST_RDY_N;
      async_up_data     <= IB_UP_DATA;
      async_up_sop_n    <= IB_UP_SOP_N;
      async_up_eop_n    <= IB_UP_EOP_N;
      async_up_src_rdy_n<= IB_UP_SRC_RDY_N;
      IB_UP_DST_RDY_N   <= async_up_dst_rdy_n;
   end generate;
   
-- -------------------------------------------------------------------------
--    Spartan IB interface
-- -------------------------------------------------------------------------

   IB_SP_TX: entity work.ib_tx8
   generic map (
      DATA_WIDTH     =>  64)
   port map (
      CLK            => trn_clk,
      RESET          => trn_reset,
      -- RX interface
      TX_DATA        => ibus_bar0_down_data,
      TX_SOP_N       => ibus_bar0_down_sop_n,
      TX_EOP_N       => ibus_bar0_down_eop_n,
      TX_SRC_RDY_N   => ibus_bar0_down_src_rdy_n,
      TX_DST_RDY_N   => ibus_bar0_down_dst_rdy_n,
      -- TX interface
      TX_PAD         => SP_TX,
      TX_RDY_N_PAD   => SP_TX_RDY
   );

   IB_SP_RX: entity work.ib_rx8
   generic map (
      DATA_WIDTH     =>  64)
   port map (
      CLK            => trn_clk,
      RXCLK          => open,
      RESET          => reset_sync,
      -- RX interface
      RX_DATA        => ibus_bar0_up_data,
      RX_SOP_N       => ibus_bar0_up_sop_n,
      RX_EOP_N       => ibus_bar0_up_eop_n,
      RX_SRC_RDY_N   => ibus_bar0_up_src_rdy_n,
      RX_DST_RDY_N   => ibus_bar0_up_dst_rdy_n,
      -- TX interface
      RX_PAD         => SP_RX,
      RX_RDY_N_PAD   => SP_RX_RDY
   );
  
   -- Synchronize the trn_reset signal to IB clock
   RESET_SYNC_PROC : process(trn_clk)
   begin
      if trn_clk'event and trn_clk = '1' then 
         reset_i    <= trn_reset;
         reset_sync <= reset_i;
      end if;  
   end process;
   
   RESET_OUT : process(trn_clk, trn_reset)
   begin
      if trn_reset = '1' then
         regiob_sp3_reset_n <= '0'; -- 
      elsif trn_clk'event and trn_clk = '1' then
         regiob_sp3_reset_n <= not trn_reset;
      end if;
   end process;
   
   SP_RST <= regiob_sp3_reset_n;
   
   INTERRUPT_LOGIC: process(trn_clk)
   begin
      if trn_clk'event and trn_clk = '1' then
         cfg_interrupt_assert_n <= '1';
         if (trn_reset = '1') or (CFG_INTERRUPT_RDY_N = '0') then
            cfg_interrupt_n <= '1';
            INTR_RDY        <= '1';
         elsif (INTERRUPT = '1') then
            cfg_interrupt_n  <= '0';
            cfg_interrupt_di <= cfg_interrupt_do(7 downto 5) & INTR_DATA(4 downto 0);
            INTR_RDY         <= '0';
         end if;
      end if;
   end process;
   
   
-- -------------------------------------------------------------------------
-- Debug - Chipscope
-- -------------------------------------------------------------------------

--   ICON_U: icon3
--   port map (
--      control0    => control0,
--      control1    => control1,
--      control2    => control2
--   );

--   RX_ILA : ila 
--   port map (
--      control     => control0,
--      clk         => trn_clk,
--      trig0       => rx_trig0, 
--      trig1       => rx_trig1
--   );
--     
--   TX_ILA : ila 
--   port map (
--      control     => control1,
--      clk         => trn_clk,
--      trig0       => tx_trig0, 
--      trig1       => tx_trig1
--   );    
--   
--   IB_ILA : ila 
--   port map (
--      control     => control2,
--      clk         => trn_clk,
--      trig0       => ib_trig0, 
--      trig1       => ib_trig1
--   );

-- rx_trig0 <= ibus_bar0.down.data;
-- rx_trig1 <= "000000000000" & ibus_bar0.down.dst_rdy_n & ibus_bar0.down.src_rdy_n & ibus_bar0.down.eop_n & ibus_bar0.down.sop_n;

-- tx_trig0 <= ibus_bar0.up.data;
-- tx_trig1 <= "000000000000" & ibus_bar0.up.dst_rdy_n & ibus_bar0.up.src_rdy_n & ibus_bar0.up.eop_n & ibus_bar0.up.sop_n;

-- -- ib_trig0 <= trn_rdata;
-- -- ib_trig1 <= trn_rbar_hit_n & "00000" & trn_rdst_rdy_n & trn_rsrc_rdy_n & trn_reof_n & trn_rsof_n;
-- --
-- -- ib_trig0 <= trn_tdata;
-- -- -- ib_trig1 <= "0000000" & "00000" & trn_tdst_rdy_n & trn_tsrc_rdy_n & trn_teof_n & trn_tsof_n;

-- --                                       PCI ID                  PCI TAG
-- -- -- ib_trig0 <= trn_tdata(63 downto 32) & debug(32 downto 17) & debug(16 downto 9) & debug(7 downto 0);
-- ib_trig0 <= trn_tdata;
-- ib_trig1 <= '0' & trn_rbar_hit_n & trn_rdst_rdy_n & trn_rsrc_rdy_n & trn_reof_n & trn_rsof_n & trn_tdst_rdy_n & trn_tsrc_rdy_n & trn_teof_n & trn_tsof_n;

-- --                                 16 (BUS,DEV,FUNC)        8 (PCI TAG)           1                   8 (Local TAG)
-- --    DEBUG <= X"0000000"&"000" & local_compl_tx_req_id & local_compl_tx_tag & local_compl_tx_rd & local_compl_tx_rtag;


-- -- ib_trig0 <= (others => '0');
-- -- ib_trig1 <= (others => '0');

end architecture behavioral;
