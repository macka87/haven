-- ebp_wrapper.vhd : Wrapper body for Xilinx PCI Express endpoint block plus core
-- Copyright (C) 2010 CESNET
-- Author(s): Pavol Korček <korcek@liberouter.org>
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


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                              Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of ebp_wrapper is

   -- -------------------------------------------------------------------------
   --    Xilinx Endpoint Block Plus version 1.14
   -- ------------------------------------------------------------------------
component endpoint_blk_plus_v1_14
   port (
      sys_reset_n             : in  std_logic;
      sys_clk                 : in  std_logic;
      refclkout               : out std_logic;
   
      pci_exp_rxn             : in  std_logic_vector(7 downto 0);
      pci_exp_rxp             : in  std_logic_vector(7 downto 0);
      pci_exp_txn             : out std_logic_vector(7 downto 0);
      pci_exp_txp             : out std_logic_vector(7 downto 0);
   
      trn_clk                 : out std_logic; 
      trn_reset_n             : out std_logic; 
      trn_lnk_up_n            : out std_logic; 
    
      trn_tsof_n              : in  std_logic;
      trn_teof_n              : in  std_logic;
      trn_td                  : in  std_logic_vector(63 downto 0);
      trn_trem_n              : in  std_logic_vector( 7 downto 0);
      trn_terrfwd_n           : in  std_logic;
      trn_tsrc_rdy_n          : in  std_logic;
      trn_tdst_rdy_n          : out std_logic;
      trn_tsrc_dsc_n          : in  std_logic;
      trn_tdst_dsc_n          : out std_logic;
      trn_tbuf_av             : out std_logic_vector(3 downto 0 );
   
      trn_rsof_n              : out std_logic;
      trn_reof_n              : out std_logic; 
      trn_rd                  : out std_logic_vector(63 downto 0);
      trn_rrem_n              : out std_logic_vector( 7 downto 0);
      trn_rerrfwd_n           : out std_logic; 
      trn_rsrc_rdy_n          : out std_logic; 
      trn_rdst_rdy_n          : in  std_logic; 
      trn_rsrc_dsc_n          : out std_logic; 
      trn_rnp_ok_n            : in  std_logic; 
      trn_rcpl_streaming_n    : in std_logic;
      trn_rbar_hit_n          : out std_logic_vector( 6 downto 0 );
      trn_rfc_ph_av           : out std_logic_vector( 7 downto 0 );
      trn_rfc_pd_av           : out std_logic_vector(11 downto 0 ); 
      trn_rfc_nph_av          : out std_logic_vector( 7 downto 0 ); 
      trn_rfc_npd_av          : out std_logic_vector(11 downto 0 ); 
   
      cfg_do                  : out std_logic_vector(31 downto 0 );
      cfg_rd_wr_done_n        : out std_logic; 
      cfg_di                  : in  std_logic_vector(31 downto 0 ); 
      cfg_dwaddr              : in  std_logic_vector( 9 downto 0 );
      cfg_wr_en_n             : in  std_logic;
      cfg_rd_en_n             : in  std_logic; 
      cfg_byte_en_n           : in  std_logic_vector( 3 downto 0 ); 
      cfg_interrupt_n         : in  std_logic;
      cfg_interrupt_rdy_n     : out std_logic;
      cfg_interrupt_mmenable  : out std_logic_vector(2 downto 0);
      cfg_interrupt_msienable : out std_logic;
      cfg_interrupt_di        : in  std_logic_vector(7 downto 0);
      cfg_interrupt_do        : out std_logic_vector(7 downto 0);
      cfg_interrupt_assert_n  : in  std_logic;
      cfg_to_turnoff_n        : out std_logic;
      cfg_bus_number          : out std_logic_vector( 7 downto 0 );
      cfg_device_number       : out std_logic_vector( 4 downto 0 );
      cfg_function_number     : out std_logic_vector( 2 downto 0 );
      cfg_status              : out std_logic_vector(15 downto 0 );
      cfg_command             : out std_logic_vector(15 downto 0 );
      cfg_dstatus             : out std_logic_vector(15 downto 0 );
      cfg_dcommand            : out std_logic_vector(15 downto 0 );
      cfg_lstatus             : out std_logic_vector(15 downto 0 );
      cfg_lcommand            : out std_logic_vector(15 downto 0 );
      cfg_pm_wake_n           : in  std_logic;
      cfg_pcie_link_state_n   : out std_logic_vector ( 2 downto 0 ); 
      cfg_trn_pending_n       : in  std_logic;
      cfg_dsn                 : in  std_logic_vector (63 downto 0 );
      fast_train_simulation_only : in std_logic;
   
      cfg_err_ecrc_n          : in  std_logic; 
      cfg_err_ur_n            : in  std_logic;
      cfg_err_cpl_rdy_n       : out std_logic;
      cfg_err_cpl_timeout_n   : in  std_logic; 
      cfg_err_cpl_unexpect_n  : in  std_logic; 
      cfg_err_cpl_abort_n     : in  std_logic; 
      cfg_err_posted_n        : in  std_logic; 
      cfg_err_cor_n           : in  std_logic; 
      cfg_err_tlp_cpl_header  : in  std_logic_vector( 47 downto 0 ); 
      cfg_err_locked_n        : in  std_logic
   );
   end component;
   
   -- System interface signals ------------------------------------------------
   signal sys_reset_n_sig     : std_logic;      -- an asynchronous input signal reset
   signal sys_clk_sig         : std_logic;      -- referece clock (100 MHz or 250MHz)
   signal refclkout_sig       : std_logic;      -- a free running global reference clock output
   
   -- PCI Express interface signals -------------------------------------------
   signal pci_exp_rxn_sig     : std_logic_vector(7 downto 0);
   signal pci_exp_rxp_sig     : std_logic_vector(7 downto 0);
   signal pci_exp_txn_sig     : std_logic_vector(7 downto 0);
   signal pci_exp_txp_sig     : std_logic_vector(7 downto 0);
   
   -- Common transaction interface signals ------------------------------------
   signal trn_clk_sig         : std_logic;      -- TRN clock (62,5/125/250MHz)
   signal trn_reset_n_sig     : std_logic;      -- TRN reset
   signal trn_reset_n_reg     : std_logic;      -- TRN reset register
   signal trn_lnk_up_n_sig    : std_logic;      -- TRN link up
   signal trn_lnk_up_n_reg    : std_logic;      -- TRN link up register
   
   -- Transmit TRN interface signals ------------------------------------------
   signal trn_tsof_n_sig      : std_logic;                        -- TRN TX start of frame
   signal trn_teof_n_sig      : std_logic;                        -- TRN TX end of frame
   signal trn_td_sig          : std_logic_vector(63 downto 0);    -- TRN TX transmit data
   signal trn_trem_n_sig      : std_logic_vector( 7 downto 0);    -- TRN TX data remainder
   signal trn_terrfwd_n_sig   : std_logic;                        -- TRN TX transmit error forward
   signal trn_tsrc_rdy_n_sig  : std_logic;                        -- TRN TX source ready
   signal trn_tdst_rdy_n_sig  : std_logic;                        -- TRN TX destination ready
   signal trn_tsrc_dsc_n_sig  : std_logic;                        -- TRN TX source discontinue
   signal trn_tdst_dsc_n_sig  : std_logic;                        -- TRN TX destination discontinue
   signal trn_tbuf_av_sig     : std_logic_vector( 3 downto 0);    -- TRN TX buffer availability
   
   -- Recieve TRN interface signals -------------------------------------------
   signal trn_rsof_n_sig     : std_logic;                        -- TRN RX start of frame
   signal trn_reof_n_sig     : std_logic;                        -- TRN RX end of frame
   signal trn_rd_sig         : std_logic_vector(63 downto 0);    -- TRN RX recieve data
   signal trn_rrem_n_sig     : std_logic_vector( 7 downto 0);    -- TRN RX data remainder
   signal trn_rerrfwd_n_sig  : std_logic;                        -- TRN RX recieve error forward
   signal trn_rsrc_rdy_n_sig : std_logic;                        -- TRN RX source ready
   signal trn_rdst_rdy_n_sig : std_logic;                        -- TRN RX destination ready
   signal trn_rsrc_dsc_n_sig : std_logic;                        -- TRN RX source discontinue
  -- signal trn_rnp_ok_n_sig   : std_logic;                        -- TRN RX non-posted OK
   signal trn_rcpl_streaming_n_sig : std_logic;                  -- TRN RX completition streaming 
   signal trn_rbar_hit_n_sig : std_logic_vector( 6 downto 0);    -- TRN RX bar hit
   signal trn_rfc_ph_av_sig  : std_logic_vector( 7 downto 0);    -- TRN RX posted header flow control credits
   signal trn_rfc_pd_av_sig  : std_logic_vector(11 downto 0);    -- TRN RX posted data flow control credits
   signal trn_rfc_nph_av_sig : std_logic_vector( 7 downto 0);    -- TRN RX non-posted header flow control credits
   signal trn_rfc_npd_av_sig : std_logic_vector(11 downto 0);    -- TRN RX non-posted data flow control credits
   
   -- Configuration interface signals -----------------------------------------
   signal cfg_do_sig                   : std_logic_vector(31 downto 0);    -- configuration data out
   signal cfg_rd_wr_done_n_sig         : std_logic;                        -- read/write done
   signal cfg_di_sig                   : std_logic_vector(31 downto 0);    -- configuration data in
   signal cfg_dwaddr_sig               : std_logic_vector( 9 downto 0);    -- dword address
   signal cfg_wr_en_n_sig              : std_logic;                        -- write enable
   signal cfg_rd_en_n_sig              : std_logic;                        -- read enable
   signal cfg_byte_en_n_sig            : std_logic_vector( 3 downto 0);    -- byte enable
   signal cfg_interrupt_n_sig          : std_logic;                        -- assert interrupt
   signal cfg_interrupt_rdy_n_sig      : std_logic;                        -- interrupt ready
   signal cfg_interrupt_mmenable_sig   : std_logic_vector( 2 downto 0);    -- multiple message enable
   signal cfg_interrupt_msienable_sig  : std_logic;                        -- MSI enable
   signal cfg_interrupt_di_sig         : std_logic_vector( 7 downto 0);    -- interrupt data input
   signal cfg_interrupt_do_sig         : std_logic_vector( 7 downto 0);    -- interrupt data output
   signal cfg_interrupt_assert_n_sig   : std_logic;                        -- assert legacy interrupt
   signal cfg_to_turnoff_n_sig         : std_logic;                        -- notifies going to turn off
   signal cfg_bus_number_sig           : std_logic_vector( 7 downto 0);    -- PCI Bus number
   signal cfg_device_number_sig        : std_logic_vector( 4 downto 0);    -- PCI Device number
   signal cfg_function_number_sig      : std_logic_vector( 2 downto 0);    -- PCI Function number
   signal cfg_status_sig               : std_logic_vector(15 downto 0);    -- status register
   signal cfg_command_sig              : std_logic_vector(15 downto 0);    -- command register
   signal cfg_dstatus_sig              : std_logic_vector(15 downto 0);    -- extended status register
   signal cfg_dcommand_sig             : std_logic_vector(15 downto 0);    -- extended command register
   signal cfg_lstatus_sig              : std_logic_vector(15 downto 0);    -- extended link status register
   signal cfg_lcommand_sig             : std_logic_vector(15 downto 0);    -- extended link command register
   signal cfg_pm_wake_n_sig            : std_logic;                        -- power management wake message
   signal cfg_pcie_link_state_n_sig    : std_logic_vector( 2 downto 0);    -- express link state
   signal cfg_trn_pending_n_sig        : std_logic;                        -- user pending transaction
   signal cfg_dsn_sig                  : std_logic_vector(63 downto 0 );   -- device serial number register
   signal fast_train_simulation_only_sig : std_logic;                      -- fast train for simulation
   
   -- Error reporting signals -------------------------------------------------
   signal cfg_err_ecrc_n_sig           : std_logic;                        -- ecrc error from user 
   signal cfg_err_ur_n_sig             : std_logic;                        -- unsupported reguest error from user
   signal cfg_err_cpl_timeout_n_sig    : std_logic;                        -- completition timeout from user
   signal cfg_err_cpl_unexpect_n_sig   : std_logic;                        -- unexpected completition from user
   signal cfg_err_cpl_abort_n_sig      : std_logic;                        -- aborted completition from user
   signal cfg_err_posted_n_sig         : std_logic;                        -- posted error from user
   signal cfg_err_cor_n_sig            : std_logic;                        -- correctable error from user
   signal cfg_err_tlp_cpl_header_sig   : std_logic_vector(47 downto 0);    -- error in specific header field from user
   signal cfg_err_cpl_rdy_n_sig        : std_logic;                        -- ready for error input 
   signal cfg_err_locked_n_sig         : std_logic;                        -- error in locked transaction from user
   
   -- some used configuration interface registers -----------------------------
   signal cfg_bus_number_reg           : std_logic_vector( 7 downto 0);
   signal cfg_device_number_reg        : std_logic_vector( 4 downto 0);
   signal cfg_function_number_reg      : std_logic_vector( 2 downto 0);
   signal cfg_dcommand_reg             : std_logic_vector(15 downto 0);

begin

-- ----------------------------------------------------------------------------
--                              Architecture body
-- ---------------------------------------------------------------------------- 

-- -------------------------------------------------------------------------
--    Xilinx Endpoint Block Plus version 1.14
-- -------------------------------------------------------------------------
-- Please make sure that this component name is 'ep'
ep: endpoint_blk_plus_v1_14
-- 'open' output signals and input signals tied 'high' or 'low' are NOT USED
   port map (
      sys_reset_n          => sys_reset_n_sig,              -- I
      sys_clk              => sys_clk_sig,                  -- I
      refclkout            => open,                         -- O

      pci_exp_rxn          => pci_exp_rxn_sig,              -- I (7:0)
      pci_exp_rxp          => pci_exp_rxp_sig,              -- I (7:0)
      pci_exp_txn          => pci_exp_txn_sig,              -- O (7:0)
      pci_exp_txp          => pci_exp_txp_sig,              -- O (7:0)

      trn_clk              => trn_clk_sig,                  -- O
      trn_reset_n          => trn_reset_n_sig,              -- O
      trn_lnk_up_n         => trn_lnk_up_n_sig,             -- O

      trn_tsof_n           => trn_tsof_n_sig,               -- I
      trn_teof_n           => trn_teof_n_sig,               -- I
      trn_td               => trn_td_sig,                   -- I (63:0)
      trn_trem_n           => trn_trem_n_sig,               -- I (7:0)
      trn_terrfwd_n        => '1', --trn_terrfwd_n_sig,     -- I
      trn_tsrc_rdy_n       => trn_tsrc_rdy_n_sig,           -- I
      trn_tdst_rdy_n       => trn_tdst_rdy_n_sig,           -- O
      trn_tsrc_dsc_n       => '1', --trn_tsrc_dsc_n_sig,    -- I
      trn_tdst_dsc_n       => open, --trn_tdst_dsc_n_sig,   -- O
      trn_tbuf_av          => trn_tbuf_av_sig,              -- O (3:0)

      trn_rsof_n           => trn_rsof_n_sig,               -- O
      trn_reof_n           => trn_reof_n_sig,               -- O
      trn_rd               => trn_rd_sig,                   -- O (63:0)
      trn_rrem_n           => trn_rrem_n_sig,               -- O
      trn_rerrfwd_n        => trn_rerrfwd_n_sig,            -- O
      trn_rsrc_rdy_n       => trn_rsrc_rdy_n_sig,           -- O
      trn_rdst_rdy_n       => trn_rdst_rdy_n_sig,           -- I
      trn_rsrc_dsc_n       => open, --trn_rsrc_dsc_n_sig,   -- O
      trn_rnp_ok_n         => '0', --trn_rnp_ok_n_sig,      -- I //bypassing prohibited
      trn_rcpl_streaming_n => '1', --trn_rcpl_streaming_n_sig,-- I
      trn_rbar_hit_n       => trn_rbar_hit_n_sig,           -- O (6:0)
      trn_rfc_ph_av        => open, --trn_rfc_ph_av_sig,    -- O (11:0)
      trn_rfc_pd_av        => open, --trn_rfc_pd_av_sig,    -- O (7:0)
      trn_rfc_nph_av       => open, --trn_rfc_nph_av_sig,   -- O (11:0)
      trn_rfc_npd_av       => open, --trn_rfc_npd_av_sig,   -- O (7:0)

      cfg_do                     => open, --cfg_do_sig,              -- O (31:0)
      cfg_rd_wr_done_n           => open, --cfg_rd_wr_done_n_sig,    -- O
      cfg_di                     => (others => '0'), --cfg_di_sig,   -- I (31:0)
      cfg_dwaddr                 => (others => '0'), --cfg_dwaddr_sig,-- I (9:0)
      cfg_wr_en_n                => '1', --cfg_wr_en_n_sig,          -- I
      cfg_rd_en_n                => '1', --cfg_rd_en_n_sig,          -- I
      cfg_byte_en_n              => (others => '0'), --cfg_byte_en_n_sig,-- I (3:0)
      cfg_interrupt_n            => cfg_interrupt_n_sig,             -- I
      cfg_interrupt_rdy_n        => cfg_interrupt_rdy_n_sig,         -- O
      cfg_interrupt_mmenable     => open, --cfg_interrupt_mmenable_sig,  -- O [2:0]
      cfg_interrupt_msienable    => open, --cfg_interrupt_msienable_sig, -- O
      cfg_interrupt_di           => cfg_interrupt_di_sig,            -- I [7:0]
      cfg_interrupt_do           => cfg_interrupt_do_sig,            -- O [7:0]
      cfg_interrupt_assert_n     => cfg_interrupt_assert_n_sig,      -- I
      cfg_to_turnoff_n           => open, --cfg_to_turnoff_n_sig,    -- O
      cfg_bus_number             => cfg_bus_number_sig,              -- O (7:0)
      cfg_device_number          => cfg_device_number_sig,           -- O (4:0)
      cfg_function_number        => cfg_function_number_sig,         -- O (2:0)
      cfg_status                 => open, --cfg_status_sig,          -- O (15:0)
      cfg_command                => open, --cfg_command_sig,         -- O (15:0)
      cfg_dstatus                => open, --cfg_dstatus_sig,         -- O (15:0)
      cfg_dcommand               => cfg_dcommand_sig,                -- O (15:0)
      cfg_lstatus                => open, --cfg_lstatus_sig,         -- O (15:0)
      cfg_lcommand               => open, --cfg_lcommand_sig,        -- O (15:0)
      cfg_pm_wake_n              => '1', --cfg_pm_wake_n_sig,        -- I
      cfg_pcie_link_state_n      => open, --cfg_pcie_link_state_n_sig,-- O (2:0)
      cfg_trn_pending_n          => '1', --cfg_trn_pending_n_sig,    -- I
      cfg_dsn                    => (others => '0'), --cfg_dsn_sig,  -- I (63:0)
      fast_train_simulation_only => '0', --fast_simulation_only_sig, -- I

      cfg_err_ecrc_n             => '1', --cfg_err_ecrc_n_sig,       -- I 
      cfg_err_ur_n               => '1', --cfg_err_ur_n_sig,         -- I 
      cfg_err_cpl_timeout_n      => '1', --cfg_err_cpl_timeout_n_sig,-- I 
      cfg_err_cpl_unexpect_n     => '1', --cfg_err_unexpect_n_sig,   -- I 
      cfg_err_cpl_abort_n        => '1', --cfg_err_cpl_abort_n_sig,  -- I 
      cfg_err_posted_n           => '1', --cfg_err_posted_n_sig,     -- I 
      cfg_err_cor_n              => '1', --cfg_err_cor_n_sig,        -- I      
      cfg_err_tlp_cpl_header     => (others => '0'), --cfg_err_tlp_cpl_header_sig-- I (47:0) 
      cfg_err_cpl_rdy_n          => open, --cfg_err_cpl_tdy_n_sig,   -- O 
      cfg_err_locked_n           => '1' --cfg_err_locked_n_sig       -- I 
   );

   -- Interface signals mapping -----------------------------------------------
   sys_reset_n_sig         <= SYS_RESET_N;
   sys_clk_sig             <= SYS_CLK;

   pci_exp_rxn_sig         <= PCI_EXP_RXN;
   pci_exp_rxp_sig         <= PCI_EXP_RXP;
   PCI_EXP_TXN             <= pci_exp_txn_sig;
   PCI_EXP_TXP             <= pci_exp_txp_sig;

   TRN_CLK                 <= trn_clk_sig;

   trn_tsof_n_sig          <= TRN_TSOF_N;    
   trn_teof_n_sig          <= TRN_TEOF_N;    
   trn_td_sig              <= TRN_TD;        
   trn_trem_n_sig          <= TRN_TREM_N;    
   trn_tsrc_rdy_n_sig      <= TRN_TSRC_RDY_N;
   TRN_TDST_RDY_N          <= trn_tdst_rdy_n_sig;
   TRN_TBUF_AV             <= trn_tbuf_av_sig;   

   TRN_RSOF_N              <= trn_rsof_n_sig;       
   TRN_REOF_N              <= trn_reof_n_sig;       
   TRN_RD                  <= TRN_RD_sig;           
   TRN_RREM_N              <= trn_rrem_n_sig;       
   TRN_RERRFWD_N           <= trn_rerrfwd_n_sig;    
   TRN_RSRC_RDY_N          <= trn_rsrc_rdy_n_sig;   
   trn_rdst_rdy_n_sig      <= TRN_RDST_RDY_N;   
   --trn_rnp_ok_n_sig        <= TRN_RNP_OK_N;     
   TRN_RBAR_HIT_N          <= trn_rbar_hit_n_sig;       

   cfg_interrupt_n_sig     <= CFG_INTERRUPT_N;        
   CFG_INTERRUPT_RDY_N     <= cfg_interrupt_rdy_n_sig;    
   cfg_interrupt_di_sig    <= CFG_INTERRUPT_DI;       
   CFG_INTERRUPT_DO        <= cfg_interrupt_do_sig;       
   cfg_interrupt_assert_n_sig<= CFG_INTERRUPT_ASSERT_N;
    

   -- Used configuration signals registered ----------------------------------- 
   USE_CFG_REGS_U : if (USE_CFG_REGS) generate
      -- register cfg_regs ------------------------------------------------------
      cfg_regsp: process(trn_clk_sig)
      begin --no need for inicialization
         if (trn_clk_sig'event AND trn_clk_sig = '1') then
            trn_reset_n_reg         <= trn_reset_n_sig;
            trn_lnk_up_n_reg        <= trn_lnk_up_n_sig;
            cfg_bus_number_reg      <= cfg_bus_number_sig;
            cfg_device_number_reg   <= cfg_device_number_sig;
            cfg_function_number_reg <= cfg_function_number_sig;
            cfg_dcommand_reg        <= cfg_dcommand_sig;
         end if;
      end process;

      TRN_RESET_N             <= trn_reset_n_reg;
      TRN_LNK_UP_N            <= trn_lnk_up_n_reg;
      CFG_BUS_NUMBER          <= cfg_bus_number_reg;        
      CFG_DEVICE_NUMBER       <= cfg_device_number_reg;     
      CFG_FUNCTION_NUMBER     <= cfg_function_number_reg;  
      CFG_DCOMMAND            <= cfg_dcommand_reg;                                               
   end generate;  -- USE_CFG_REGS 

   -- Used configuration signals not registred --------------------------------
   NO_USE_CFG_REGS_U : if (not USE_CFG_REGS) generate
      TRN_RESET_N             <= trn_reset_n_sig;
      TRN_LNK_UP_N            <= trn_lnk_up_n_sig;
      CFG_BUS_NUMBER          <= cfg_bus_number_sig;        
      CFG_DEVICE_NUMBER       <= cfg_device_number_sig;     
      CFG_FUNCTION_NUMBER     <= cfg_function_number_sig;  
      CFG_DCOMMAND            <= cfg_dcommand_sig;      
   end generate;  -- NO_USE_CFG_REGS

end architecture behavioral;
