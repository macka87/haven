-- combov2_pci.vhd : PCIe and Spartan interface for the ComboLXT card
-- Copyright (C) 2008 CESNET
-- Author(s): Stepan Friedl <friedl@liberouter.org>
--            Pavol Korcek <korcek@liberouter.org>
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

architecture behavioral of cv2_pci is

  -------------------------------------------------------------------
  --   Component with Xilinx PCI Express endpoint block plus core
  -------------------------------------------------------------------
   component ebp_wrapper is
      port (
         -- System interface signals ------------------------------------------
         SYS_RESET_N             : in  std_logic;                    -- an asynchronous input signal reset
         SYS_CLK                 : in  std_logic;                    -- referece clock (100 MHz or 250MHz)
   
         -- PCI Express interface signals -------------------------------------
         PCI_EXP_RXN             : in  std_logic_vector(7 downto 0); -- negative RX Express lanes
         PCI_EXP_RXP             : in  std_logic_vector(7 downto 0); -- possitive RX Express lanes
         PCI_EXP_TXN             : out std_logic_vector(7 downto 0); -- negative TX Express lanes
         PCI_EXP_TXP             : out std_logic_vector(7 downto 0); -- possitive TX Express lanes
   
         -- Common transaction interface signals ------------------------------
         TRN_CLK                 : out std_logic;                    -- TRN clock (62,5/125/250MHz)
         TRN_RESET_N             : out std_logic;                    -- TRN reset
         TRN_LNK_UP_N            : out std_logic;                    -- TRN link up
   
         -- Transmit TRN interface signals ------------------------------------
         TRN_TSOF_N              : in  std_logic;                    -- TRN TX start of frame
         TRN_TEOF_N              : in  std_logic;                    -- TRN TX end of frame
         TRN_TD                  : in  std_logic_vector(63 downto 0);-- TRN TX transmit data
         TRN_TREM_N              : in  std_logic_vector(7 downto 0); -- TRN TX data remainder
         TRN_TSRC_RDY_N          : in  std_logic;                    -- TRN TX source ready
         TRN_TDST_RDY_N          : out std_logic;                    -- TRN TX destination ready
         TRN_TBUF_AV             : out std_logic_vector(3 downto 0); -- TRN TX buffer availability
         
         -- Recieve TRN interface signals -------------------------------------
         TRN_RSOF_N              : out std_logic;                    -- TRN RX start of frame
         TRN_REOF_N              : out std_logic;                    -- TRN RX end of frame
         TRN_RD                  : out std_logic_vector(63 downto 0);-- TRN RX recieve data
         TRN_RREM_N              : out std_logic_vector(7 downto 0); -- TRN RX data remainder
         TRN_RERRFWD_N           : out std_logic;                    -- TRN RX recieve error forward
         TRN_RSRC_RDY_N          : out std_logic;                    -- TRN RX source ready
         TRN_RDST_RDY_N          : in  std_logic;                    -- TRN RX destination ready
--          TRN_RNP_OK_N            : in  std_logic;                    -- TRN RX non-posted OK
         TRN_RBAR_HIT_N          : out std_logic_vector(6 downto 0); -- TRN RX bar hit
   
         -- Configuration interface signals -----------------------------------
         CFG_INTERRUPT_N         : in  std_logic;                    -- assert interrupt
         CFG_INTERRUPT_RDY_N     : out std_logic;                    -- interrupt ready
         CFG_INTERRUPT_DI        : in  std_logic_vector( 7 downto 0);-- interrupt data input
         CFG_INTERRUPT_DO        : out std_logic_vector( 7 downto 0);-- interrupt data output
         CFG_INTERRUPT_ASSERT_N  : in  std_logic;                    -- assert legacy interrupt
         CFG_BUS_NUMBER          : out std_logic_vector( 7 downto 0);-- PCI Bus number
         CFG_DEVICE_NUMBER       : out std_logic_vector( 4 downto 0);-- PCI Device number
         CFG_FUNCTION_NUMBER     : out std_logic_vector( 2 downto 0);-- PCI Function number
         CFG_DCOMMAND            : out std_logic_vector(15 downto 0) -- extended command register
      );
   end component;
 
  -------------------------------------------------------------------
  --           RX ASFIFO component on TRN interface
  -------------------------------------------------------------------
   component rx_asfifo_bram
      port (
	      din      : in std_logic_vector(81 downto 0);
	      rd_clk   : in std_logic;
	      rd_en    : in std_logic;
	      rst      : in std_logic;
	      wr_clk   : in std_logic;
	      wr_en    : in std_logic;
	      dout     : out std_logic_vector(81 downto 0);
	      empty    : out std_logic;
	      full     : out std_logic;
	      valid    : out std_logic
      );
   end component;

  -------------------------------------------------------------------
  --           TX ASFIFO component on TRN interface
  -------------------------------------------------------------------
   component tx_asfifo_bram
      port (
   	   din      : in std_logic_vector(73 downto 0);
   	   rd_clk   : in std_logic;
   	   rd_en    : in std_logic;
   	   rst      : in std_logic;
   	   wr_clk   : in std_logic;
   	   wr_en    : in std_logic;
   	   dout     : out std_logic_vector(73 downto 0);
   	   empty    : out std_logic;
   	   full     : out std_logic;
   	   valid    : out std_logic
      );
   end component;

-- ----------------------------------------------------------------------------
--                         Signals declaration 
-- ----------------------------------------------------------------------------

   -- Clocks & resets 
   signal regiob_sp3_reset_n                    : std_logic;
   signal reset_i                               : std_logic;
   signal reset_sync                            : std_logic;
   signal ib_clk_sig                            : std_logic;
   signal ib_rst_sig                            : std_logic;
   signal ib_rst_reg                            : std_logic;
   signal sp_clk_sig                            : std_logic;
   signal sp_rst_sig                            : std_logic;
   signal sp_rst_reg                            : std_logic;
   signal trn_clk                               : std_logic; 
   signal trn_reset_n                           : std_logic; 
   signal trn_reset                             : std_logic; 
   signal trn_reset_reg                         : std_logic;
   signal bridge_trn_clk                        : std_logic;
   signal bridge_trn_reset_n                    : std_logic;

   -- PCIe Bridge <-> IB Switch port0
   signal ibus0_down_data                       : std_logic_vector(63 downto 0);
   signal ibus0_down_sop_n                      : std_logic;
   signal ibus0_down_eop_n                      : std_logic;
   signal ibus0_down_src_rdy_n                  : std_logic;
   signal ibus0_down_dst_rdy_n                  : std_logic;
   signal ibus0_up_data                         : std_logic_vector(63 downto 0);
   signal ibus0_up_sop_n                        : std_logic;
   signal ibus0_up_eop_n                        : std_logic;
   signal ibus0_up_src_rdy_n                    : std_logic;
   signal ibus0_up_dst_rdy_n                    : std_logic;

   -- pipe for ASFIFO <-> IB Switch
   signal async_pipe_ibus_bar0_down_data        : std_logic_vector(63 downto 0);
   signal async_pipe_ibus_bar0_down_sop_n       : std_logic;
   signal async_pipe_ibus_bar0_down_eop_n       : std_logic;
   signal async_pipe_ibus_bar0_down_src_rdy_n   : std_logic;
   signal async_pipe_ibus_bar0_down_dst_rdy_n   : std_logic;
   signal async_pipe_ibus_bar0_up_data          : std_logic_vector(63 downto 0);
   signal async_pipe_ibus_bar0_up_sop_n         : std_logic;
   signal async_pipe_ibus_bar0_up_eop_n         : std_logic;
   signal async_pipe_ibus_bar0_up_src_rdy_n     : std_logic;
   signal async_pipe_ibus_bar0_up_dst_rdy_n     : std_logic;

   -- Switch <-> registers to netcope
   signal reg_ib_down_data        : std_logic_vector(63 downto 0);
   signal reg_ib_down_sop_n       : std_logic;
   signal reg_ib_down_eop_n       : std_logic;
   signal reg_ib_down_src_rdy_n   : std_logic;
   signal reg_ib_down_dst_rdy_n   : std_logic;
   signal reg_ib_up_data          : std_logic_vector(63 downto 0);
   signal reg_ib_up_sop_n         : std_logic;
   signal reg_ib_up_eop_n         : std_logic;
   signal reg_ib_up_src_rdy_n     : std_logic;
   signal reg_ib_up_dst_rdy_n     : std_logic;

   -- Switch <-> ASFIFO  
   signal async_ibus_bar0_down_data             : std_logic_vector(63 downto 0);
   signal async_ibus_bar0_down_sop_n            : std_logic;
   signal async_ibus_bar0_down_eop_n            : std_logic;
   signal async_ibus_bar0_down_src_rdy_n        : std_logic;
   signal async_ibus_bar0_down_dst_rdy_n        : std_logic;
   signal async_ibus_bar0_up_data               : std_logic_vector(63 downto 0);
   signal async_ibus_bar0_up_sop_n              : std_logic;
   signal async_ibus_bar0_up_eop_n              : std_logic;
   signal async_ibus_bar0_up_src_rdy_n          : std_logic;
   signal async_ibus_bar0_up_dst_rdy_n          : std_logic;

   -- ASFIFO <-> Spartan
   signal sp_ibus_bar0_down_data                : std_logic_vector(63 downto 0);
   signal sp_ibus_bar0_down_sop_n               : std_logic;
   signal sp_ibus_bar0_down_eop_n               : std_logic;
   signal sp_ibus_bar0_down_src_rdy_n           : std_logic;
   signal sp_ibus_bar0_down_dst_rdy_n           : std_logic;
   signal sp_ibus_bar0_up_data                  : std_logic_vector(63 downto 0);
   signal sp_ibus_bar0_up_sop_n                 : std_logic;
   signal sp_ibus_bar0_up_eop_n                 : std_logic;
   signal sp_ibus_bar0_up_src_rdy_n             : std_logic;
   signal sp_ibus_bar0_up_dst_rdy_n             : std_logic;
     
   -- PCIE CFG   
   signal bridge_cfg_bus_number                 : std_logic_vector( 7 downto 0);
   signal bridge_cfg_device_number              : std_logic_vector( 4 downto 0);
   signal bridge_cfg_function_number            : std_logic_vector( 2 downto 0);
   signal bridge_cfg_dcommand                   : std_logic_vector(15 downto 0);
   signal core_cfg_interrupt_n                  : std_logic;
   signal core_cfg_interrupt_rdy_n              : std_logic;
   signal core_cfg_interrupt_assert_n           : std_logic;
   signal core_cfg_interrupt_di                 : std_logic_vector(7 downto 0);
   signal core_cfg_interrupt_do                 : std_logic_vector(7 downto 0);
 
   -- PCIE RX TRN
   signal core_trn_rd                           : std_logic_vector(63 downto 0);
   signal bridge_trn_rd                         : std_logic_vector(63 downto 0);
   signal core_trn_rrem_n                       : std_logic_vector( 7 downto 0);     
   signal bridge_trn_rrem_n                     : std_logic_vector( 7 downto 0);
   signal core_trn_rsof_n                       : std_logic;
   signal bridge_trn_rsof_n                     : std_logic;
   signal core_trn_reof_n                       : std_logic;
   signal bridge_trn_reof_n                     : std_logic;
   signal core_trn_rsrc_rdy_n                   : std_logic;
   signal bridge_trn_rsrc_rdy_n                 : std_logic;
   signal core_trn_rdst_rdy_n                   : std_logic;
   signal bridge_trn_rdst_rdy_n                 : std_logic;
   signal core_trn_rerrfwd_n                    : std_logic;
   signal bridge_trn_rerrfwd_n                  : std_logic;
   signal core_trn_rbar_hit_n                   : std_logic_vector( 6 downto 0);
   signal bridge_trn_rbar_hit_n                 : std_logic_vector( 6 downto 0);
   signal core_trn_lnk_up_n                     : std_logic;
   signal bridge_trn_lnk_up_n                   : std_logic;
   --signal core_trn_rnp_ok_n                     : std_logic;
--    signal bridge_trn_rnp_ok_n                   : std_logic;

   -- PCIE TX TRN
   signal core_trn_td                           : std_logic_vector(63 downto 0);
   signal bridge_trn_td                         : std_logic_vector(63 downto 0);
   signal core_trn_trem_n                       : std_logic_vector( 7 downto 0);
   signal bridge_trn_trem_n                     : std_logic_vector( 7 downto 0);
   signal core_trn_tsof_n                       : std_logic;
   signal bridge_trn_tsof_n                     : std_logic;   
   signal core_trn_teof_n                       : std_logic;
   signal bridge_trn_teof_n                     : std_logic;
   signal core_trn_tsrc_rdy_n                   : std_logic;
   signal bridge_trn_tsrc_rdy_n                 : std_logic;
   signal core_trn_tdst_rdy_n                   : std_logic;
   signal bridge_trn_tdst_rdy_n                 : std_logic;
   signal core_trn_tbuf_av                      : std_logic_vector( 3 downto 0);
   signal bridge_trn_tbuf_av                    : std_logic_vector( 3 downto 0);

   -- signals for RX asfifo
   signal rx_din_sig                            : std_logic_vector(81 downto 0);
   signal rx_rd_en_sig                          : std_logic;
   signal rx_wr_en_sig                          : std_logic;
   signal rx_dout_sig                           : std_logic_vector(81 downto 0);
   signal rx_empty_sig                          : std_logic;
   signal rx_full_sig                           : std_logic;
   signal rx_valid_sig_n                        : std_logic;

   -- signals for TX asfifo
   signal tx_din_sig                            : std_logic_vector(73 downto 0);
   signal tx_rd_en_sig                          : std_logic;
   signal tx_wr_en_sig                          : std_logic;
   signal tx_dout_sig                           : std_logic_vector(73 downto 0);
   signal tx_empty_sig                          : std_logic;
   signal tx_full_sig                           : std_logic;
   signal tx_valid_sig_n                        : std_logic;

   -- TRN_TBUF_AV asynchronous handling
   signal trn_tbuf_rdy_reg                      : std_logic;
   signal trn_tbuf_rdy_comp_sig                 : std_logic;
   signal trn_tbuf_rdy_start_sig                : std_logic;
   signal trn_tbuf_rdy_end_sig                  : std_logic;

   -- rx pcie core <-> rx asfifo register
   signal rx_pipe_in_data                       : std_logic_vector(79 downto 0);
   signal rx_pipe_in_src_rdy_n                  : std_logic; 
   signal rx_pipe_out_data                      : std_logic_vector(79 downto 0);
   signal rx_pipe_out_sof_n                     : std_logic;
   signal rx_pipe_out_eof_n                     : std_logic;
   signal rx_pipe_out_src_rdy_n                 : std_logic;
   signal rx_pipe_out_dst_rdy_n                 : std_logic;
  
   -- tx pcie core <-> tx asfico register
   signal tx_pipe_in_data                       : std_logic_vector(71 downto 0);
   signal tx_pipe_in_src_rdy_n                  : std_logic;
   signal tx_pipe_in_dst_rdy_n                  : std_logic;
   signal tx_pipe_out_data                      : std_logic_vector(71 downto 0);
   signal tx_pipe_out_src_rdy_n                 : std_logic;
   signal tx_pipe_out_dst_rdy_n                 : std_logic;

   -- interrupt fifo signals
   signal interrupt_reg                         : std_logic := '0';
   signal ififo_full                            : std_logic;
   signal ififo_empty                           : std_logic;
   signal ififo_rd                              : std_logic;


   -- ATTRIBUTES --------------------------------------------------------------
   attribute buffer_type:string;
   attribute buffer_type of trn_clk:signal is "none";
   attribute buffer_type of sp_clk_sig:signal is "none"; 
   attribute buffer_type of ib_clk_sig:signal is "none"; 
   attribute buffer_type of bridge_trn_clk:signal is "none"; 

   -- These constants are no more used! All were replaced by one generic USE_TRN_ASYNC.
   -- But it is possible to change it, to set asynchronous only TRN RX, TRN TX and so on.
   constant USE_TRN_RX_ASYNC_CONST           : boolean := true;   -- TRN RX interface from PCIe core
   constant USE_TRN_TX_ASYNC_CONST           : boolean := true;   -- TRN TX interface to PCIe core
   constant GEN_TRN_RX_PIPE_CONST            : boolean := true;   -- only with USE_TRN_RX_ASYNC_CONST
   constant GEN_TRN_TX_PIPE_CONST            : boolean := true;   -- only with USE_TRN_TX_ASYNC_CONST
   constant USE_SPARTAN_ASYNC_CONST          : boolean := true;   -- interface to Spartan FPGA
   constant USE_INTERRUPT_LOGIC_ASYNC_CONST  : boolean := true;   -- interrupt logic asynchronous fifo 
   constant USE_ASYNC_CLOCKS_CONST           : boolean := true;   -- independent/same clocks?

   -- USED CONSTANTS
   constant USE_SPARTAN_PIPE_UP_CONST        : boolean := true;   -- pipe ib switch<->asfifo on up
   constant USE_SPARTAN_PIPE_DOWN_CONST      : boolean := true;   -- pipe ib switch<->asfifo on down

begin

   -- -------------------------------------------------------------------------
   --                         PCIE to IB TOP LEVEL                           --
   -- ------------------------------------------------------------------------- 
   trn_reset               <= not trn_reset_n;
   PCIE_CORE_TRN_RST       <= trn_reset; --_reg;
   --PCIE_CORE_TRN_CLK       <= trn_clk;

--    -- register ib_rst_reg and trn_reset_reg -----------------------------------
--    ib_rst_regp: process(IB_CLK, IB_RST, trn_reset)
--    begin
--       if (IB_RST = '1') then
--          ib_rst_reg <= '1';
--          trn_reset_reg <= '1';
--       elsif (IB_CLK'event and IB_CLK = '1') then
--          ib_rst_reg <= IB_RST;
--          trn_reset_reg <= trn_reset;
--       end if;
--    end process;

--    -- register sp_rst_reg -----------------------------------------------------
--    sp_rst_regp: process(SP_CLK, SP_RESET)
--    begin
--       if (SP_RESET = '1') then
--          sp_rst_reg <= '1';
--       elsif (SP_CLK'event and SP_CLK = '1') then
--          sp_rst_reg <= SP_RESET; 
--       end if;
--    end process;

   -- normal use clock
   USE_ASYNC_CLOCKS : if (USE_TRN_ASYNC) generate 
      ib_clk_sig           <= IB_CLK;
      ib_rst_sig           <= IB_RST; --ib_rst_reg;
      
      sp_clk_sig           <= SP_CLK;
      sp_rst_sig           <= SP_RESET; --sp_rst_reg;

      bridge_trn_clk       <= IB_CLK;
      bridge_trn_reset_n   <= not IB_RST; --not ib_rst_reg;
   end generate;

   -- testing purpose clocks
   NO_USE_ASYNC_CLOCKS : if (not USE_TRN_ASYNC) generate
      ib_clk_sig           <= trn_clk;
      ib_rst_sig           <= trn_reset;
      
      sp_clk_sig           <= trn_clk;
      sp_rst_sig           <= trn_reset;

      bridge_trn_clk       <= trn_clk;
      bridge_trn_reset_n   <= trn_reset_n; 
   end generate;

   ----------------------------------------------------------------------------
   --    Component with Xilinx PCI Express endpoint block plus core
   ----------------------------------------------------------------------------
   EBP_WRAPPER_U: ebp_wrapper
      port map (
         -- System interface signals ------------------------------------------
         SYS_RESET_N       => PCIE_RST_N,       
         SYS_CLK           => PCIE_CLK,
         -- PCI Express interface signals -------------------------------------
         PCI_EXP_RXN       => PCI_EXP_RXN,
         PCI_EXP_RXP       => PCI_EXP_RXP, 
         PCI_EXP_TXN       => PCI_EXP_TXN,     
         PCI_EXP_TXP       => PCI_EXP_TXP,      
         -- Common transaction interface signals ------------------------------
         TRN_CLK           => trn_clk, 
         TRN_RESET_N       => trn_reset_n,    
         TRN_LNK_UP_N      => core_trn_lnk_up_n,    
         -- Transmit TRN interface signals ------------------------------------
         TRN_TSOF_N        => core_trn_tsof_n,    
         TRN_TEOF_N        => core_trn_teof_n,    
         TRN_TD            => core_trn_td,    
         TRN_TREM_N        => core_trn_trem_n,    
         TRN_TSRC_RDY_N    => core_trn_tsrc_rdy_n,    
         TRN_TDST_RDY_N    => core_trn_tdst_rdy_n,    
         TRN_TBUF_AV       => core_trn_tbuf_av,    
         -- Recieve TRN interface signals -------------------------------------
         TRN_RSOF_N        => core_trn_rsof_n,  
         TRN_REOF_N        => core_trn_reof_n,  
         TRN_RD            => core_trn_rd,  
         TRN_RREM_N        => core_trn_rrem_n,  
         TRN_RERRFWD_N     => core_trn_rerrfwd_n,  
         TRN_RSRC_RDY_N    => core_trn_rsrc_rdy_n,  
         TRN_RDST_RDY_N    => core_trn_rdst_rdy_n,  
        -- TRN_RNP_OK_N      => core_trn_rnp_ok_n,  
         TRN_RBAR_HIT_N    => core_trn_rbar_hit_n,  
         -- Configuration interface signals -----------------------------------
         CFG_INTERRUPT_N        => core_cfg_interrupt_n,           
         CFG_INTERRUPT_RDY_N    => core_cfg_interrupt_rdy_n,
         CFG_INTERRUPT_DI       => core_cfg_interrupt_di,
         CFG_INTERRUPT_DO       => core_cfg_interrupt_do,
         CFG_INTERRUPT_ASSERT_N => core_cfg_interrupt_assert_n,
         CFG_BUS_NUMBER         => bridge_cfg_bus_number,
         CFG_DEVICE_NUMBER      => bridge_cfg_device_number,
         CFG_FUNCTION_NUMBER    => bridge_cfg_function_number,
         CFG_DCOMMAND           => bridge_cfg_dcommand
      );

   -- -------------------------------------------------------------------------
   --    PCI Express Bridge
   -- -------------------------------------------------------------------------
   PCIE2IB_BRIDGE_U: entity work.PCIE2IB_BRIDGE 
   generic map (
      ENABLE_ALIGN_UNIT => false,
      BRIDGE_BASE_ADDR  => X"F0000000",
      DISCARD_UNSUPPORTED_IB_TRANS => true,
      -- BAR base addresses
      BAR0_REMAP        => X"C0000000",
      BAR1_REMAP        => X"C0000000",
      BAR2_REMAP        => X"00000000",
      BAR3_REMAP        => X"00000000",
      BAR4_REMAP        => X"C0010000", 
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
      trn_clk                 => bridge_trn_clk,
      trn_reset_n             => bridge_trn_reset_n,
      trn_lnk_up_n            => bridge_trn_lnk_up_n,
      -- ----------- PCI Express TLP TX Interface ------------------------------
      trn_tsof_n              => bridge_trn_tsof_n,    
      trn_teof_n              => bridge_trn_teof_n,
      trn_td                  => bridge_trn_td,     
      trn_trem_n              => bridge_trn_trem_n,    
      trn_tsrc_rdy_n          => bridge_trn_tsrc_rdy_n,
      trn_tdst_rdy_n          => bridge_trn_tdst_rdy_n,
      trn_tbuf_av             => bridge_trn_tbuf_av,
      -- ----------- PCI Express TLP RX Interface ------------------------------
      trn_rsof_n              => bridge_trn_rsof_n,
      trn_reof_n              => bridge_trn_reof_n,
      trn_rd                  => bridge_trn_rd,
      trn_rrem_n              => bridge_trn_rrem_n,
      trn_rerrfwd_n           => bridge_trn_rerrfwd_n,
      trn_rsrc_rdy_n          => bridge_trn_rsrc_rdy_n,
      trn_rdst_rdy_n          => bridge_trn_rdst_rdy_n,
      --trn_rnp_ok_n            => bridge_trn_rnp_ok_n,
      trn_rbar_hit_n          => bridge_trn_rbar_hit_n,
      -- ----------- PCI Express Host Configuration interface ------------------
      cfg_bus_number          => bridge_cfg_bus_number,
      cfg_device_number       => bridge_cfg_device_number,
      cfg_function_number     => bridge_cfg_function_number,
      cfg_dcommand            => bridge_cfg_dcommand,
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
 
   --core_trn_rnp_ok_n <= bridge_trn_rnp_ok_n; 

   -- ------------------------------------------------------------------------- 
   --    TRN RX
   -- -------------------------------------------------------------------------

   -- asynchronous
   USE_TRN_RX_ASYNC : if (USE_TRN_ASYNC) generate

      -- input RX PIPE --------------------------------------------------------
      GEN_TRN_RX_PIPE : if (USE_TRN_ASYNC) generate

         -- pipeline input data
         rx_pipe_in_data         <= core_trn_rbar_hit_n & core_trn_rrem_n & core_trn_rd & core_trn_rerrfwd_n;

         rx_pipe_in_src_rdy_n    <= '0' when (core_trn_lnk_up_n = '0' and core_trn_rsrc_rdy_n = '0') else
                                    '1';

         TRNRX_PIPE_U : entity work.IB_PIPE
            generic map (
               DATA_WIDTH     => 80
            )   
            port map (
               -- Common interface --------------------------------------------
               CLK            => trn_clk,
               RESET          => trn_reset,
               -- Input interface ---------------------------------------------
               IN_DATA        => rx_pipe_in_data,
               IN_SOF_N       => core_trn_rsof_n,
               IN_EOF_N       => core_trn_reof_n,
               IN_SRC_RDY_N   => rx_pipe_in_src_rdy_n, 
               IN_DST_RDY_N   => core_trn_rdst_rdy_n,
               -- Output interface --------------------------------------------
               OUT_DATA       => rx_pipe_out_data,
               OUT_SOF_N      => rx_pipe_out_sof_n,
               OUT_EOF_N      => rx_pipe_out_eof_n,
               OUT_SRC_RDY_N  => rx_pipe_out_src_rdy_n,
               OUT_DST_RDY_N  => rx_pipe_out_dst_rdy_n
            );  

         -- asfifo input data
         rx_din_sig              <= rx_pipe_out_data & rx_pipe_out_eof_n & rx_pipe_out_sof_n;

         rx_wr_en_sig            <= '1' when (rx_pipe_out_src_rdy_n = '0') else
                                    '0';
         rx_pipe_out_dst_rdy_n   <= '0' when (rx_full_sig = '0') else
                                    '1';
      end generate; -- GEN_TRN_RX_PIPE 

      -- NO input RX PIPE -----------------------------------------------------
      NO_GEN_TRN_RX_PIPE : if (not USE_TRN_ASYNC) generate

         -- asfifo input data
         rx_din_sig           <= core_trn_rbar_hit_n & core_trn_rrem_n & core_trn_rd 
                                 & core_trn_rerrfwd_n & core_trn_reof_n & core_trn_rsof_n;
         rx_wr_en_sig         <= '1' when (core_trn_lnk_up_n = '0' and core_trn_rsrc_rdy_n = '0') else
                                 '0';
         core_trn_rdst_rdy_n  <= '0' when (rx_full_sig = '0') else
                                 '1';
      end generate; -- NO_GEN_TRN_RX_PIPE

      -- from PCIe core to PCIe BRIDGE
      RX_ASFIFO_TRN_U: rx_asfifo_bram
      port map(
         din      => rx_din_sig,
         rd_clk   => ib_clk_sig,
         rd_en    => rx_rd_en_sig,
         rst      => trn_reset,
         wr_clk   => trn_clk,
         wr_en    => rx_wr_en_sig,
         dout     => rx_dout_sig,
         empty    => rx_empty_sig,
         full     => rx_full_sig,
         valid    => rx_valid_sig_n
      );
            
      bridge_trn_rbar_hit_n   <= rx_dout_sig(81 downto 75);
      bridge_trn_rrem_n       <= rx_dout_sig(74 downto 67);
      bridge_trn_rd           <= rx_dout_sig(66 downto 3);
      bridge_trn_rerrfwd_n    <= rx_dout_sig(2);
      bridge_trn_reof_n       <= rx_dout_sig(1);
      bridge_trn_rsof_n       <= rx_dout_sig(0);

      rx_rd_en_sig            <= '1' when (bridge_trn_rdst_rdy_n = '0') else
                                 '0';
      bridge_trn_rsrc_rdy_n   <= '0' when (rx_empty_sig = '0') else
                                 '1';  

   end generate; -- USE_TRN_RX_ASYNC


   -- direct
   NO_USE_TRN_RX_ASYNC : if (not USE_TRN_ASYNC) generate

      bridge_trn_rd           <= core_trn_rd;            -- 64  
      bridge_trn_rrem_n       <= core_trn_rrem_n;        --  8   
      bridge_trn_rsof_n       <= core_trn_rsof_n;        --  1  
      bridge_trn_reof_n       <= core_trn_reof_n;        --  1   
      bridge_trn_rsrc_rdy_n   <= core_trn_rsrc_rdy_n;    -- wr
      core_trn_rdst_rdy_n     <= bridge_trn_rdst_rdy_n;  -- rd 
      bridge_trn_rerrfwd_n    <= core_trn_rerrfwd_n;     --  1
      bridge_trn_rbar_hit_n   <= core_trn_rbar_hit_n;    --  7 
      --                                              --------
      --                                                    82
   end generate; -- NO_USE_TRN_RX_ASYNC

   
   -- ------------------------------------------------------------------------- 
   --    TRN TX
   -- -------------------------------------------------------------------------
   
   -- asynchronous
   USE_TRN_TX_ASYNC : if (USE_TRN_ASYNC) generate

      tx_din_sig              <= bridge_trn_trem_n & bridge_trn_td & bridge_trn_teof_n & bridge_trn_tsof_n;
      tx_wr_en_sig            <= '1' when (bridge_trn_tsrc_rdy_n = '0') else
                                 '0'; 
      bridge_trn_tdst_rdy_n   <= '0' when (tx_full_sig = '0') else
                                 '1';

      -- from PCIe BRIDGE to PCIe core
      TX_ASFIFO_TRN_U: tx_asfifo_bram
      port map(
      	   din      => tx_din_sig,
            rd_clk   => trn_clk,
      	   rd_en    => tx_rd_en_sig,
      	   rst      => trn_reset,
       	   wr_clk   => ib_clk_sig,
      	   wr_en    => tx_wr_en_sig,
      	   dout     => tx_dout_sig,
      	   empty    => tx_empty_sig,
      	   full     => tx_full_sig,
      	   valid    => tx_valid_sig_n
         );
     
      -- common
      bridge_trn_tbuf_av      <= "1111";  -- in bridge always available
      bridge_trn_lnk_up_n     <= '0';  
      trn_tbuf_rdy_comp_sig   <= '1' when (core_trn_tbuf_av = "1111") else
                                 '0';

      -- output TX PIPE --------------------------------------------------------
      GEN_TRN_TX_PIPE : if (USE_TRN_ASYNC) generate

         -- pipeline input data
         tx_pipe_in_data         <= tx_dout_sig(73 downto 66) & tx_dout_sig(65 downto 2);


         tx_pipe_in_src_rdy_n    <= '0' when ( tx_empty_sig = '0' and
                                               (trn_tbuf_rdy_reg = '1' or
                                               (trn_tbuf_rdy_start_sig = '1' and trn_tbuf_rdy_comp_sig = '1') )
                                             ) else
                                    '1';

         tx_rd_en_sig            <= '1' when (tx_pipe_in_dst_rdy_n = '0' and 
                                                (trn_tbuf_rdy_reg = '1' or
                                                (trn_tbuf_rdy_start_sig = '1' and trn_tbuf_rdy_comp_sig = '1') ) 
                                             ) else
                                    '0';

         TRNTX_PIPE_U : entity work.IB_PIPE
            generic map (
               DATA_WIDTH     => 72
            )   
            port map (
               -- Common interface --------------------------------------------
               CLK            => trn_clk,
               RESET          => trn_reset,
               -- Input interface ---------------------------------------------
               IN_DATA        => tx_pipe_in_data,
               IN_SOF_N       => tx_dout_sig(0),
               IN_EOF_N       => tx_dout_sig(1),
               IN_SRC_RDY_N   => tx_pipe_in_src_rdy_n, 
               IN_DST_RDY_N   => tx_pipe_in_dst_rdy_n, 
               -- Output interface --------------------------------------------
               OUT_DATA       => tx_pipe_out_data,
               OUT_SOF_N      => core_trn_tsof_n,
               OUT_EOF_N      => core_trn_teof_n,
               OUT_SRC_RDY_N  => core_trn_tsrc_rdy_n, 
               OUT_DST_RDY_N  => tx_pipe_out_dst_rdy_n
            );  


         core_trn_trem_n      <= tx_pipe_out_data(71 downto 64);
         core_trn_td          <= tx_pipe_out_data(63 downto 0);


         tx_pipe_out_dst_rdy_n   <= '0' when (core_trn_lnk_up_n = '0' and core_trn_tdst_rdy_n = '0') else 
                                    '1';

         trn_tbuf_rdy_start_sig  <= '1' when ((tx_dout_sig(0) = '0') and (tx_valid_sig_n = '0')) else
                                    '0';

         trn_tbuf_rdy_end_sig    <= '1' when ((tx_dout_sig(1) = '0') and (tx_valid_sig_n = '0')) else
                                    '0';

         -- register trn_tbuf_rdy_reg --------------------------------------------
         trn_tbuf_rdyp: process(trn_reset, trn_clk)
         begin
            if (trn_reset = '1') then
               trn_tbuf_rdy_reg <= '0';
            elsif (trn_clk'event and trn_clk = '1') then
               -- SOP and buffer in PCIe core ready => transmit ready
               if ( trn_tbuf_rdy_start_sig = '1' and trn_tbuf_rdy_comp_sig = '1') then
                  trn_tbuf_rdy_reg <= '1';
              -- EOP and core can accept data => next transmit NOT ready
               elsif ( trn_tbuf_rdy_end_sig = '1' and tx_pipe_in_dst_rdy_n = '0') then
                  trn_tbuf_rdy_reg <= '0';
               end if;
            end if;
         end process;

      end generate; -- GEN_TRN_TX_PIPE

       -- NO input TX PIPE -----------------------------------------------------
      NO_GEN_TRN_TX_PIPE : if (not USE_TRN_ASYNC) generate

         core_trn_trem_n         <= tx_dout_sig(73 downto 66);
         core_trn_td             <= tx_dout_sig(65 downto 2);
         core_trn_teof_n         <= tx_dout_sig(1);
         core_trn_tsof_n         <= tx_dout_sig(0);

         tx_rd_en_sig            <= '1' when (core_trn_lnk_up_n = '0' and core_trn_tdst_rdy_n = '0' and 
                                               (trn_tbuf_rdy_reg = '1' or
                                               (trn_tbuf_rdy_start_sig = '1' and trn_tbuf_rdy_comp_sig = '1') ) 
                                             ) else
                                    '0';

         core_trn_tsrc_rdy_n     <= '0' when ( tx_empty_sig = '0' and
                                               (trn_tbuf_rdy_reg = '1' or
                                               (trn_tbuf_rdy_start_sig = '1' and trn_tbuf_rdy_comp_sig = '1') )
                                             ) else
                                    '1';


         trn_tbuf_rdy_start_sig  <= '1' when ((core_trn_tsof_n = '0') and (tx_valid_sig_n = '0')) else
                                    '0';

         trn_tbuf_rdy_end_sig    <= '1' when ((core_trn_teof_n = '0') and (tx_valid_sig_n = '0')) else
                                    '0';

         -- register trn_tbuf_rdy_reg --------------------------------------------
         trn_tbuf_rdyp: process(trn_reset, trn_clk)
         begin
            if (trn_reset = '1') then
               trn_tbuf_rdy_reg <= '0';
            elsif (trn_clk'event and trn_clk = '1') then
               -- SOP and buffer in PCIe core ready => transmit ready
               if ( trn_tbuf_rdy_start_sig = '1' and trn_tbuf_rdy_comp_sig = '1') then
                  trn_tbuf_rdy_reg <= '1';
              -- EOP and core can accept data => next transmit NOT ready
               elsif ( trn_tbuf_rdy_end_sig = '1' and core_trn_tdst_rdy_n = '0') then
                  trn_tbuf_rdy_reg <= '0';
               end if;
            end if;
         end process;

      end generate; -- NO_GEN_TRN_TX_PIPE
   end generate; -- USE_TRN_TX_ASYNC  

   -- direct
   NO_USE_TRN_TX_ASYNC : if (not USE_TRN_ASYNC) generate

      core_trn_td             <= bridge_trn_td;          -- 64
      core_trn_trem_n         <= bridge_trn_trem_n;      --  8
      core_trn_tsof_n         <= bridge_trn_tsof_n;      --  1
      core_trn_teof_n         <= bridge_trn_teof_n;      --  1
      core_trn_tsrc_rdy_n     <= bridge_trn_tsrc_rdy_n;  -- wr  
      bridge_trn_tdst_rdy_n   <= core_trn_tdst_rdy_n;    -- rd
      --                                             ---------
      --                                                    74      
      bridge_trn_tbuf_av      <= core_trn_tbuf_av;
      bridge_trn_lnk_up_n     <= core_trn_lnk_up_n;  

   end generate; -- NO_USE_TRN_TX_ASYNC


   -- -------------------------------------------------------------------------
   --    IB SWITCH (User IB and BAR0 selection)
   -- -------------------------------------------------------------------------
       
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
      IB_CLK        => ib_clk_sig,  
      IB_RESET      => ib_rst_sig,
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
      -- To Netcope
      PORT1_DOWN_DATA      => reg_ib_down_data,      
      PORT1_DOWN_SOP_N     => reg_ib_down_sop_n,    
      PORT1_DOWN_EOP_N     => reg_ib_down_eop_n,    
      PORT1_DOWN_SRC_RDY_N => reg_ib_down_src_rdy_n,
      PORT1_DOWN_DST_RDY_N => reg_ib_down_dst_rdy_n,
      PORT1_UP_DATA        => reg_ib_up_data,      
      PORT1_UP_SOP_N       => reg_ib_up_sop_n,    
      PORT1_UP_EOP_N       => reg_ib_up_eop_n,    
      PORT1_UP_SRC_RDY_N   => reg_ib_up_src_rdy_n,
      PORT1_UP_DST_RDY_N   => reg_ib_up_dst_rdy_n,
      -- To Spartan
      PORT2_DOWN_DATA      => async_ibus_bar0_down_data,     
      PORT2_DOWN_SOP_N     => async_ibus_bar0_down_sop_n,    
      PORT2_DOWN_EOP_N     => async_ibus_bar0_down_eop_n,    
      PORT2_DOWN_SRC_RDY_N => async_ibus_bar0_down_src_rdy_n,
      PORT2_DOWN_DST_RDY_N => async_ibus_bar0_down_dst_rdy_n,
      PORT2_UP_DATA        => async_ibus_bar0_up_data,     
      PORT2_UP_SOP_N       => async_ibus_bar0_up_sop_n,    
      PORT2_UP_EOP_N       => async_ibus_bar0_up_eop_n,    
      PORT2_UP_SRC_RDY_N   => async_ibus_bar0_up_src_rdy_n,
      PORT2_UP_DST_RDY_N   => async_ibus_bar0_up_dst_rdy_n
   ); 
  
   -- -------------------------------------------------------------------------
   --    Pipe to/from IB
   -- -------------------------------------------------------------------------

   PIPE_NETCOPE_DOWN_U : entity work.IB_PIPE
      generic map (
         DATA_WIDTH     => 64
      )   
      port map (
         -- Common interface --------------------------------------------
         CLK            => ib_clk_sig,
         RESET          => ib_rst_sig,
         -- Input interface ---------------------------------------------
         IN_DATA        => reg_ib_down_data,
         IN_SOF_N       => reg_ib_down_sop_n,
         IN_EOF_N       => reg_ib_down_eop_n,
         IN_SRC_RDY_N   => reg_ib_down_src_rdy_n, 
         IN_DST_RDY_N   => reg_ib_down_dst_rdy_n, 
         -- Output interface --------------------------------------------
         OUT_DATA       => IB_DOWN_DATA,
         OUT_SOF_N      => IB_DOWN_SOP_N,
         OUT_EOF_N      => IB_DOWN_EOP_N,
         OUT_SRC_RDY_N  => IB_DOWN_SRC_RDY_N, 
         OUT_DST_RDY_N  => IB_DOWN_DST_RDY_N
      );

   PIPE_NETCOPE_UP_U : entity work.IB_PIPE
      generic map (
         DATA_WIDTH     => 64
      )   
      port map (
         -- Common interface --------------------------------------------
         CLK            => ib_clk_sig,
         RESET          => ib_rst_sig,
         -- Input interface ---------------------------------------------
         IN_DATA        => IB_UP_DATA,
         IN_SOF_N       => IB_UP_SOP_N,
         IN_EOF_N       => IB_UP_EOP_N,
         IN_SRC_RDY_N   => IB_UP_SRC_RDY_N, 
         IN_DST_RDY_N   => IB_UP_DST_RDY_N, 
         -- Output interface --------------------------------------------
         OUT_DATA       => reg_ib_up_data,
         OUT_SOF_N      => reg_ib_up_sop_n,
         OUT_EOF_N      => reg_ib_up_eop_n,
         OUT_SRC_RDY_N  => reg_ib_up_src_rdy_n, 
         OUT_DST_RDY_N  => reg_ib_up_dst_rdy_n
      );


   -- -------------------------------------------------------------------------
   --    Spartan IB interface
   -- -------------------------------------------------------------------------

   -- Use async FIFOs to connect Spartan  -------------------------------------
   USE_SPARTAN_ASYNC : if (USE_TRN_ASYNC) generate
      USE_SPARTAN_PIPE_DOWN : if (USE_SPARTAN_PIPE_DOWN_CONST) generate
         UP_PIPE_SP_PIPE_U : entity work.IB_PIPE
               generic map (
                  DATA_WIDTH     => 64
               )   
               port map (
                  -- Common interface --------------------------------------------
                  CLK            => ib_clk_sig,
                  RESET          => ib_rst_sig,
                  -- Input interface ---------------------------------------------
                  IN_DATA        => async_ibus_bar0_down_data,
                  IN_SOF_N       => async_ibus_bar0_down_sop_n,
                  IN_EOF_N       => async_ibus_bar0_down_eop_n,
                  IN_SRC_RDY_N   => async_ibus_bar0_down_src_rdy_n, 
                  IN_DST_RDY_N   => async_ibus_bar0_down_dst_rdy_n, 
                  -- Output interface --------------------------------------------
                  OUT_DATA       => async_pipe_ibus_bar0_down_data,
                  OUT_SOF_N      => async_pipe_ibus_bar0_down_sop_n,
                  OUT_EOF_N      => async_pipe_ibus_bar0_down_eop_n,
                  OUT_SRC_RDY_N  => async_pipe_ibus_bar0_down_src_rdy_n, 
                  OUT_DST_RDY_N  => async_pipe_ibus_bar0_down_dst_rdy_n
               );
      end generate;

      NO_USE_SPARTAN_PIPE_DOWN : if (not USE_SPARTAN_PIPE_DOWN_CONST) generate
         async_pipe_ibus_bar0_down_data      <= async_ibus_bar0_down_data;
         async_pipe_ibus_bar0_down_sop_n     <= async_ibus_bar0_down_sop_n;
         async_pipe_ibus_bar0_down_eop_n     <= async_ibus_bar0_down_eop_n;
         async_pipe_ibus_bar0_down_src_rdy_n <= async_ibus_bar0_down_src_rdy_n; 
         async_ibus_bar0_down_dst_rdy_n      <= async_pipe_ibus_bar0_down_dst_rdy_n;
      end generate;

      -- from IB Switch to Spartan
      DOWN_ASFIFO_SP_U : entity work.ib_asfifo_64b
         port map (
            RX_CLK         => ib_clk_sig,
            RX_RESET       => ib_rst_sig,
            TX_CLK         => sp_clk_sig,
            TX_RESET       => sp_rst_sig,
            RX_DATA        => async_pipe_ibus_bar0_down_data,
            RX_EOP_N       => async_pipe_ibus_bar0_down_eop_n,
            RX_SOP_N       => async_pipe_ibus_bar0_down_sop_n,
            RX_SRC_RDY_N   => async_pipe_ibus_bar0_down_src_rdy_n,
            RX_DST_RDY_N   => async_pipe_ibus_bar0_down_dst_rdy_n,
            TX_DATA        => sp_ibus_bar0_down_data,
            TX_EOP_N       => sp_ibus_bar0_down_eop_n,
            TX_SOP_N       => sp_ibus_bar0_down_sop_n,
            TX_SRC_RDY_N   => sp_ibus_bar0_down_src_rdy_n,
            TX_DST_RDY_N   => sp_ibus_bar0_down_dst_rdy_n
         );
      USE_SPARTAN_PIPE_UP : if (USE_SPARTAN_PIPE_UP_CONST) generate
         UP_PIPE_SP_PIPE_U : entity work.IB_PIPE
               generic map (
                  DATA_WIDTH     => 64
               )   
               port map (
                  -- Common interface --------------------------------------------
                  CLK            => ib_clk_sig,
                  RESET          => ib_rst_sig,
                  -- Input interface ---------------------------------------------
                  IN_DATA        => async_pipe_ibus_bar0_up_data,
                  IN_SOF_N       => async_pipe_ibus_bar0_up_sop_n,
                  IN_EOF_N       => async_pipe_ibus_bar0_up_eop_n,
                  IN_SRC_RDY_N   => async_pipe_ibus_bar0_up_src_rdy_n, 
                  IN_DST_RDY_N   => async_pipe_ibus_bar0_up_dst_rdy_n, 
                  -- Output interface --------------------------------------------
                  OUT_DATA       => async_ibus_bar0_up_data,
                  OUT_SOF_N      => async_ibus_bar0_up_sop_n,
                  OUT_EOF_N      => async_ibus_bar0_up_eop_n,
                  OUT_SRC_RDY_N  => async_ibus_bar0_up_src_rdy_n, 
                  OUT_DST_RDY_N  => async_ibus_bar0_up_dst_rdy_n
               ); 
      end generate;

      NO_USE_SPARTAN_PIPE_UP : if (not USE_SPARTAN_PIPE_UP_CONST) generate
         async_ibus_bar0_up_data          <= async_pipe_ibus_bar0_up_data;
         async_ibus_bar0_up_sop_n         <= async_pipe_ibus_bar0_up_sop_n;
         async_ibus_bar0_up_eop_n         <= async_pipe_ibus_bar0_up_eop_n;
         async_ibus_bar0_up_src_rdy_n     <= async_pipe_ibus_bar0_up_src_rdy_n; 
         async_pipe_ibus_bar0_up_dst_rdy_n<= async_ibus_bar0_up_dst_rdy_n;
      end generate;

      -- from Spartan to IB Switch
      UP_ASFIFO_SP_U : entity work.ib_asfifo_64b
         port map (
            RX_CLK         => sp_clk_sig,
            RX_RESET       => sp_rst_sig,
            TX_CLK         => ib_clk_sig,
            TX_RESET       => ib_rst_sig,
            RX_DATA        => sp_ibus_bar0_up_data,
            RX_EOP_N       => sp_ibus_bar0_up_eop_n,
            RX_SOP_N       => sp_ibus_bar0_up_sop_n,
            RX_SRC_RDY_N   => sp_ibus_bar0_up_src_rdy_n,
            RX_DST_RDY_N   => sp_ibus_bar0_up_dst_rdy_n,
            TX_DATA        => async_pipe_ibus_bar0_up_data,
            TX_EOP_N       => async_pipe_ibus_bar0_up_eop_n,
            TX_SOP_N       => async_pipe_ibus_bar0_up_sop_n,
            TX_SRC_RDY_N   => async_pipe_ibus_bar0_up_src_rdy_n,
            TX_DST_RDY_N   => async_pipe_ibus_bar0_up_dst_rdy_n
         );

   end generate; -- USE_SPARTAN_ASYNC

   -- DO NOT Use async FIFOs to connect Spartan -------------------------------
   NO_USE_SPARTAN_ASYNC : if (not USE_TRN_ASYNC) generate 

      -- direct interconnection
      sp_ibus_bar0_down_data              <= async_ibus_bar0_down_data;
      sp_ibus_bar0_down_sop_n             <= async_ibus_bar0_down_sop_n;
      sp_ibus_bar0_down_eop_n             <= async_ibus_bar0_down_eop_n;
      sp_ibus_bar0_down_src_rdy_n         <= async_ibus_bar0_down_src_rdy_n;
      async_ibus_bar0_down_dst_rdy_n      <= sp_ibus_bar0_down_dst_rdy_n;

      -- direct interconnection
      async_ibus_bar0_up_data             <= sp_ibus_bar0_up_data;
      async_ibus_bar0_up_sop_n            <= sp_ibus_bar0_up_sop_n;
      async_ibus_bar0_up_eop_n            <= sp_ibus_bar0_up_eop_n;
      async_ibus_bar0_up_src_rdy_n        <= sp_ibus_bar0_up_src_rdy_n;
      sp_ibus_bar0_up_dst_rdy_n           <= async_ibus_bar0_up_dst_rdy_n;

   end generate; -- NO_USE_SPARTAN_ASYNC

   -- Spartan TX
   IB_SP_TX: entity work.ib_tx8
   generic map (
      DATA_WIDTH     =>  64)
   port map (
      CLK            => sp_clk_sig,
      RESET          => sp_rst_sig,
      -- RX interface
      TX_DATA        => sp_ibus_bar0_down_data,
      TX_SOP_N       => sp_ibus_bar0_down_sop_n,
      TX_EOP_N       => sp_ibus_bar0_down_eop_n,
      TX_SRC_RDY_N   => sp_ibus_bar0_down_src_rdy_n,
      TX_DST_RDY_N   => sp_ibus_bar0_down_dst_rdy_n,
      -- TX interface
      TX_PAD         => SP_TX,
      TX_RDY_N_PAD   => SP_TX_RDY
   );

   -- Spartan RX
   IB_SP_RX: entity work.ib_rx8
   generic map (
      DATA_WIDTH     =>  64)
   port map (
      CLK            => sp_clk_sig,
      RXCLK          => open,
      RESET          => reset_sync,
      -- RX interface
      RX_DATA        => sp_ibus_bar0_up_data,
      RX_SOP_N       => sp_ibus_bar0_up_sop_n,
      RX_EOP_N       => sp_ibus_bar0_up_eop_n,
      RX_SRC_RDY_N   => sp_ibus_bar0_up_src_rdy_n,
      RX_DST_RDY_N   => sp_ibus_bar0_up_dst_rdy_n,
      -- TX interface
      RX_PAD         => SP_RX
   );

   -- Synchronize the reset signal to correct clock
   RESET_SYNC_PROC : process(sp_clk_sig)
   begin
      if sp_clk_sig'event and sp_clk_sig = '1' then 
         reset_i    <= sp_rst_sig;
         reset_sync <= reset_i;
      end if;  
   end process;

   RESET_OUT : process(sp_clk_sig, sp_rst_sig)
   begin
      if sp_rst_sig = '1' then
         regiob_sp3_reset_n <= '0';
      elsif sp_clk_sig'event and sp_clk_sig = '1' then
         regiob_sp3_reset_n <= not sp_rst_sig;
      end if;
   end process;

   SP_RST <= regiob_sp3_reset_n;
  
   -- -------------------------------------------------------------------------
   --    Interrupt handling (TRN clock <-> IB clock)
   -- -------------------------------------------------------------------------
   
   -- Asynchronous interrupt handling -----------------------------------------
   USE_INTERRUPT_LOGIC_ASYNC : if (USE_TRN_ASYNC) generate
   
      INTERRUPT_FIFO: entity work.asfifo
      generic map (
          ITEMS        => 8,
          DATA_WIDTH   => 5,
          STATUS_WIDTH => 2
      )
      port map (
         RESET  => trn_reset,
         -- Write interface
         CLK_WR => ib_clk_sig,
         DI     => INTR_DATA(4 downto 0),
         WR     => interrupt_reg, --INTERRUPT,
         FULL   => ififo_full,
         STATUS => open,
         -- Read interface
         CLK_RD => trn_clk,
         DO     => core_cfg_interrupt_di(4 downto 0),
         RD     => ififo_rd,
         EMPTY  => ififo_empty
      );      
      
      INTERRUPT_REGp: process(ib_clk_sig)
      begin
         if ib_clk_sig'event and ib_clk_sig = '1' then
            interrupt_reg <= INTERRUPT;
         end if;
      end process;

 
      INTR_RDY             <= not ififo_full;
      ififo_rd             <= not core_cfg_interrupt_rdy_n;
      core_cfg_interrupt_n <= ififo_empty;
      core_cfg_interrupt_di(7 downto 5) <= core_cfg_interrupt_do(7 downto 5);
      
   end generate; -- ASYNC_INTERRUPT_LOGIC

   -- No asynchronous interrupt handling --------------------------------------
   NO_USE_INTERRUPT_LOGIC_ASYNC : if (not USE_TRN_ASYNC) generate

      INTERRUPT_LOGIC: process(trn_clk)
      begin
         if trn_clk'event and trn_clk = '1' then
            core_cfg_interrupt_assert_n <= '1';
            if (trn_reset = '1') or (core_cfg_interrupt_rdy_n = '0') then
               core_cfg_interrupt_n <= '1';
               INTR_RDY        <= '1';
            elsif (INTERRUPT = '1') then
               core_cfg_interrupt_n  <= '0';
               core_cfg_interrupt_di <= core_cfg_interrupt_do(7 downto 5) & INTR_DATA(4 downto 0);
               INTR_RDY         <= '0';
            end if;
         end if;
      end process;

   end generate; -- NO_ASYNC_INTERRUPT_LOGIC

end architecture behavioral;

