--
-- pcie2ib_bridge.vhd : PCI Express to Internal Bus bridge
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
-- DOC: htts://www.liberouter.org/trac/netcope/wiki/IBRoot_doc
-- 

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                   ENTITY DECLARATION -- PCIe to IB Bridge                 --
-- ----------------------------------------------------------------------------

entity PCIE2IB_BRIDGE is 
   generic(
      -- enable align unit for G2LR not aligned transaction 
      ENABLE_ALIGN_UNIT             : boolean := false;
      -- base address on internal bus address space
      BRIDGE_BASE_ADDR              : std_logic_vector(31 downto 0) := X"FFFFFFF0"; 
      -- local buffer tag width (must be <1,8>)
      LOCAL_TAG_WIDTH               : integer := 6;
      -- global buffer tag width, specification allows only width of 5 (5th bit is LF)
      GLOBAL_TAG_WIDTH 	            : integer := 4;
      -- discard unsupported transactions (set to true with GICS) 
      DISCARD_UNSUPPORTED_IB_TRANS  : boolean := false; 

      -- BAR base addresses
      BAR0_REMAP        : std_logic_vector(31 downto 0) := X"01000000"; -- BAR0 base address for PCIE->IB transalation
      BAR1_REMAP        : std_logic_vector(31 downto 0) := X"02000000"; -- BAR1 base address for PCIE->IB transalation
      BAR2_REMAP        : std_logic_vector(31 downto 0) := X"03000000"; -- BAR2 base address for PCIE->IB transalation
      BAR3_REMAP        : std_logic_vector(31 downto 0) := X"04000000"; -- BAR3 base address for PCIE->IB transalation
      BAR4_REMAP        : std_logic_vector(31 downto 0) := X"05000000"; -- BAR4 base address for PCIE->IB transalation
      BAR5_REMAP        : std_logic_vector(31 downto 0) := X"06000000"; -- BAR5 base address for PCIE->IB transalation       
      EXP_ROM_REMAP     : std_logic_vector(31 downto 0) := X"0A000000"; -- ROM  base address for PCIE->IB transalation

      -- BAR base addresses masks
      BAR0_MASK         : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR0 mask for PCIE->IB transalation
      BAR1_MASK         : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR1 mask for PCIE->IB transalation
      BAR2_MASK         : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR2 mask for PCIE->IB transalation
      BAR3_MASK         : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR3 mask for PCIE->IB transalation
      BAR4_MASK         : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR4 mask for PCIE->IB transalation
      BAR5_MASK         : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR5 mask for PCIE->IB transalation       
      EXP_ROM_MASK      : std_logic_vector(31 downto 0) := X"00FFFFFF"  -- ROM  mask for PCIE->IB transalation             
   );
   port (
      -- Common transaction interface signals ---------------------------------
      TRN_CLK                 : in  std_logic;                       -- TRN clock (62,5/125/250MHz)
      TRN_RESET_N             : in  std_logic;                       -- TRN reset
      TRN_LNK_UP_N            : in  std_logic;                       -- TRN link up

      -- Transmit TRN interface signals ---------------------------------------
      TRN_TSOF_N              : out std_logic;                       -- TRN TX start of frame
      TRN_TEOF_N              : out std_logic;                       -- TRN TX end of frame
      TRN_TD                  : out std_logic_vector(63 downto 0);   -- TRN TX transmit data
      TRN_TREM_N              : out std_logic_vector(7 downto 0);    -- TRN TX data remainder
      TRN_TSRC_RDY_N          : out std_logic;                       -- TRN TX source ready
      TRN_TDST_RDY_N          : in  std_logic;                       -- TRN TX destination ready
      TRN_TBUF_AV             : in  std_logic_vector(3 downto 0);    -- TRN TX buffer availability
      
      -- Recieve TRN interface signals ----------------------------------------
      TRN_RSOF_N              : in  std_logic;                       -- TRN RX start of frame
      TRN_REOF_N              : in  std_logic;                       -- TRN RX end of frame
      TRN_RD                  : in  std_logic_vector(63 downto 0);   -- TRN RX recieve data
      TRN_RREM_N              : in  std_logic_vector(7 downto 0);    -- TRN RX data remainder
      TRN_RERRFWD_N           : in  std_logic;                       -- TRN RX recieve error forward
      TRN_RSRC_RDY_N          : in  std_logic;                       -- TRN RX source ready
      TRN_RDST_RDY_N          : out std_logic;                       -- TRN RX destination ready
--       TRN_RNP_OK_N            : out std_logic;                       -- TRN RX non-posted OK
      TRN_RBAR_HIT_N          : in  std_logic_vector(6 downto 0);    -- TRN RX bar hit

      -- Configuration interface signals --------------------------------------
      CFG_BUS_NUMBER          : in  std_logic_vector( 7 downto 0);   -- PCI Bus number
      CFG_DEVICE_NUMBER       : in  std_logic_vector( 4 downto 0);   -- PCI Device number
      CFG_FUNCTION_NUMBER     : in  std_logic_vector( 2 downto 0);   -- PCI Function number
      CFG_DCOMMAND            : in  std_logic_vector(15 downto 0);   -- extended command register
	 
      -- ----------- Internal Bus TX interface ---------------------------------
      TX_DATA                  : out std_logic_vector( 63 downto 0 ); -- Data or Header
      TX_SOP_N                 : out std_logic;                       -- Start of Packet
      TX_EOP_N                 : out std_logic;                       -- End of Packet
      TX_SRC_RDY_N             : out std_logic;                       -- Source Ready
      TX_DST_RDY_N             : in  std_logic;                       -- Destination Ready

	   -- ----------- Internal Bus RX interface ---------------------------------
      RX_DATA                  : in  std_logic_vector( 63 downto 0 ); -- Data or Header
      RX_SOP_N                 : in  std_logic;                       -- Start of Packet
      RX_EOP_N                 : in  std_logic;                       -- End of Packet
      RX_SRC_RDY_N             : in  std_logic;                       -- Source Ready
      RX_DST_RDY_N             : out std_logic                        -- Destination Ready
);
end entity PCIE2IB_BRIDGE;



-- ----------------------------------------------------------------------------
--               ARCHITECTURE DECLARATION  --  PCIe to IB Bridge             --
-- ----------------------------------------------------------------------------

architecture pcie2ib_bridge_arch of PCIE2IB_BRIDGE is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal trn_reset                        : std_logic;               -- Reset active high
   
   signal rx_dec_out_data                  : std_logic_vector( 63 downto 0 ); -- Data or Header
   signal rx_dec_out_sop_n                 : std_logic;                       -- Start of Packet
   signal rx_dec_out_eop_n                 : std_logic;                       -- End of Packet
   signal rx_dec_out_src_rdy_n             : std_logic;                       -- Source Ready
   signal rx_dec_out_dst_rdy_n             : std_logic;                       -- Destination Ready
--    signal rx_dec_out_read_trans_en_n       : std_logic;                       -- Enable Read transaction receiving

   signal cmpl_buf_read_trans_en_n         : std_logic;
   
	signal local_compl_rx_tag   		       : std_logic_vector( 7 downto 0);   -- Transaction Tag
	signal local_compl_rx_wr_0              : std_logic;                       -- Write Request 0
	signal local_compl_rx_req_id 	          : std_logic_vector(15 downto 0);   -- Requester ID (BUS, DEVICE, FUNCTION)
	signal local_compl_rx_wr_1              : std_logic;                       -- Write Request 1
	signal local_compl_rx_allow             : std_logic;                       -- Allow to write
	signal local_compl_rx_local_tag         : std_logic_vector( 7 downto 0);   -- Local Tag
   signal local_compl_tx_tag 	             : std_logic_vector( 7 downto 0);   -- Transaction Tag     
   signal local_compl_tx_req_id            : std_logic_vector(15 downto 0);   -- Requester ID (BUS, DEVICE, FUNCTION)
   signal local_compl_tx_rd                : std_logic;                       -- Read Request
   signal local_compl_tx_rtag 	          : std_logic_vector( 7 downto 0);   -- Read Address
	signal local_compl_rx_full 		       : std_logic;                       -- Local Buffer Full
--    signal local_compl_trans_en_n           : std_logic;                       -- Enable Transactions
   signal local_compl_status               : std_logic_vector( 8 downto 0);   -- Status

   signal global_compl_rx_local_addr       : std_logic_vector(31 downto 0);   -- Local Address     
   signal global_compl_rx_local_tag        : std_logic_vector( 7 downto 0);   -- Local Tag     
   signal global_compl_rx_rd               : std_logic;                       -- Read Request
   signal global_compl_rx_global_tag       : std_logic_vector( 7 downto 0);   -- Read Address
   signal global_compl_rx_last_cpl         : std_logic;                       -- Last Completion
   signal global_compl_rx_len_cpl          : std_logic_vector(11 downto 0);   -- Completion Length
   signal global_compl_tx_local_addr       : std_logic_vector(31 downto 0);   -- Local Address
   signal global_compl_tx_local_tag        : std_logic_vector( 7 downto 0);   -- Local Tag
   signal global_compl_tx_wr               : std_logic;                       -- Write Request
   signal global_compl_tx_allow            : std_logic;                       -- Allow to write
   signal global_compl_tx_rtag             : std_logic_vector( 7 downto 0);   -- Global Tag
   signal global_compl_tx_full             : std_logic;                       -- Global Buffer full 
   signal global_compl_trans_en_n          : std_logic;                       -- Enable Transactions
   signal global_compl_status              : std_logic_vector( 8 downto 0);   -- Status

   signal ib_dec_out_data                  : std_logic_vector( 63 downto 0 ); -- Data or Header
   signal ib_dec_out_sop_n                 : std_logic;                       -- Start of Packet
   signal ib_dec_out_eop_n                 : std_logic;                       -- End of Packet
   signal ib_dec_out_src_rdy_n             : std_logic;                       -- Source Ready
   signal ib_dec_out_dst_rdy_n             : std_logic;                       -- Destination Ready
   signal ib_dec_out_dw4                   : std_logic;                       -- Source Ready
   signal ib_dec_out_dw4_vld               : std_logic;                       -- Destination Ready

begin

    trn_reset                 <= not trn_reset_n;
   -- -------------------------------------------------------------------------
   --              SYSTEM BUS PACKET DECODER                                 --
   -- -------------------------------------------------------------------------
   PCIE_RX_DECODER_U : entity work.PCIE_RX_DECODER
     generic map (
       INPUT_REG_EN     => true,
       OUTPUT_REG_EN    => false,
       -- BAR base addresses
       BRIDGE_BASE_ADDR => BRIDGE_BASE_ADDR, -- BRIDGE Base Address
       BAR0_REMAP       => BAR0_REMAP,       -- BAR0 base address for PCIE->IB transalation
       BAR1_REMAP       => BAR1_REMAP,       -- BAR1 base address for PCIE->IB transalation
       BAR2_REMAP       => BAR2_REMAP,       -- BAR2 base address for PCIE->IB transalation
       BAR3_REMAP       => BAR3_REMAP,       -- BAR3 base address for PCIE->IB transalation
       BAR4_REMAP       => BAR4_REMAP,       -- BAR4 base address for PCIE->IB transalation
       BAR5_REMAP       => BAR5_REMAP,       -- BAR5 base address for PCIE->IB transalation       
       EXP_ROM_REMAP    => EXP_ROM_REMAP,    -- ROM  base address for PCIE->IB transalation
       -- BAR base addresses masks
       BAR0_MASK        => BAR0_MASK,        -- BAR0 mask for PCIE->IB transalation
       BAR1_MASK        => BAR1_MASK,        -- BAR1 mask for PCIE->IB transalation
       BAR2_MASK        => BAR2_MASK,        -- BAR2 mask for PCIE->IB transalation
       BAR3_MASK        => BAR3_MASK,        -- BAR3 mask for PCIE->IB transalation
       BAR4_MASK        => BAR4_MASK,        -- BAR4 mask for PCIE->IB transalation
       BAR5_MASK        => BAR5_MASK,        -- BAR5 mask for PCIE->IB transalation       
       EXP_ROM_MASK     => EXP_ROM_MASK      -- ROM  mask for PCIE->IB transalation             
       ) 
    port map (
      -- PCI Express Common signals -------------------------------------------
      TRN_RESET_N    => trn_reset_n,
      TRN_CLK        => trn_clk,
   
      -- PCI Express RX interface ---------------------------------------------
      -- Basic signals
      TRN_RBAR_HIT_N        => trn_rbar_hit_n,            -- BAR Hit ([0] -BAR0, [6] - Expansion ROM Address
      TRN_RSOF_N            => trn_rsof_n,                -- Start-of-Frame (SOF)
      TRN_REOF_N            => trn_reof_n,                -- End-of-Frame (EOF)
      TRN_RD                => trn_rd,                    -- Data
      TRN_RREM_N            => trn_rrem_n,                -- Data Remainder (only 00000000 (valid on [63:0]) or 00001111 (valid on [63:32])
      TRN_RSRC_RDY_N        => trn_rsrc_rdy_n,            -- Source Ready
      TRN_RDST_RDY_N        => trn_rdst_rdy_n,            -- Destination Ready
      -- Error and advanced signals
      TRN_RERRFWD_N         => trn_rerrfwd_n,             -- Error Forward (Asserted by the core for entire packet - remove packet)
--       TRN_RNP_OK_N          => trn_rnp_ok_n,              -- Receive Non-Posted OK (Set by IB generator)

      -- IB Packet Generator Interface --------------------------------------
      -- Data and header interface
      DATA                  => rx_dec_out_data,           -- Data or Header
      SOP_N                 => rx_dec_out_sop_n,          -- Start of Packet
      EOP_N                 => rx_dec_out_eop_n,          -- End of Packet
      SRC_RDY_N             => rx_dec_out_src_rdy_n,      -- Source Ready
      DST_RDY_N             => rx_dec_out_dst_rdy_n      -- Destination Ready
--       READ_TRANS_EN_N       => rx_dec_out_read_trans_en_n -- Enable Read transaction receiving
      );

   -- -------------------------------------------------------------------------
   --              ITERNAL BUS PACKET GENERATOR                              --
   -- -------------------------------------------------------------------------
   PCIE_IB_GENERATOR_U : entity work.PCIE_IB_GENERATOR
     generic map (
      INPUT_PIPE	      => true,
      OUTPUT_PIPE	      => true,
      ENABLE_ALIGN_UNIT => ENABLE_ALIGN_UNIT  
      )
     port map (
      -- PCI Express Common signals -------------------------------------------
      TRN_RESET_N          => trn_reset_n,
      TRN_CLK              => trn_clk,

      -- RX Decoder interface ---------------------------------------------
      DEC_DATA             => rx_dec_out_data,           -- Data or Header
      DEC_SOP_N            => rx_dec_out_sop_n,          -- Start of Packet
      DEC_EOP_N            => rx_dec_out_eop_n,          -- End of Packet
      DEC_SRC_RDY_N        => rx_dec_out_src_rdy_n,      -- Source Ready
      DEC_DST_RDY_N        => rx_dec_out_dst_rdy_n,      -- Destination Ready
--       DEC_READ_TRANS_EN_N  => rx_dec_out_read_trans_en_n,-- Enable Read transaction receiving

      -- Write interface ------------------------------------------------------
	   LCB_TAG              => local_compl_rx_tag,	      -- Transaction Tag
	   LCB_WR_0	            => local_compl_rx_wr_0,       -- Write Request 0
	   LCB_REQ_ID	         => local_compl_rx_req_id,		-- Requester ID (BUS, DEVICE, FUNCTION)
	   LCB_WR_1		         => local_compl_rx_wr_1,	      -- Write Request 1
      LCB_ALLOW		      =>	local_compl_rx_allow,	   -- Allow to write
	   LCB_LOCAL_TAG        => local_compl_rx_local_tag,  -- Local Tag
	   --LCB_FULL		         => local_compl_rx_full,       -- Local Buffer Full
--       LCB_TRANS_EN_N       => local_compl_trans_en_n,    -- Enable Transactions
	   -- Read Interface -------------------------------------------------------
      GCB_LOCAL_ADDR       => global_compl_rx_local_addr, -- Local Address     
      GCB_LOCAL_TAG        => global_compl_rx_local_tag,	 -- Local Tag     
      GCB_RD     	         =>	global_compl_rx_rd,		    -- Read Request
      GCB_GLOBAL_TAG       => global_compl_rx_global_tag, -- Read Address
	   GCB_LAST_CPL	      => global_compl_rx_last_cpl,	 -- Last Completion
	   GCB_LEN_CPL	         => global_compl_rx_len_cpl,    -- Completion Length

      -- IB Decoder interface ---------------------------------------------
      -- Data and header interface
      DATA                 => TX_DATA,                    -- Data or Header
      SOP_N                => TX_SOP_N,                   -- Start of Packet
      EOP_N                => TX_EOP_N,                   -- End of Packet
      SRC_RDY_N            => TX_SRC_RDY_N,               -- Source Ready
      DST_RDY_N            => TX_DST_RDY_N                -- Destination Ready
      );

    -- -------------------------------------------------------------------------
    --              LOCAL COMPLETION BUFFER                                   --
    -- -------------------------------------------------------------------------
    LOCAL_COMPL_BUF_U : entity work.LOCAL_COMPL_BUF
      generic map (
       LOCAL_TAG_WIDTH   => LOCAL_TAG_WIDTH     -- 'Local' Tag width
     )
     port map (
      -- clock & reset --------------------------------------------------------
      CLK               => trn_clk,  	         -- FPGA clock
      RESET             => trn_reset,	         -- Reset active high

	  -- Write interface ------------------------------------------------------
	   RX_TAG            => local_compl_rx_tag, 		   -- Transaction Tag
	   RX_WR_0		      => local_compl_rx_wr_0,       -- Write Request 0
	   RX_REQ_ID	      => local_compl_rx_req_id,	   -- Requester ID (BUS, DEVICE, FUNCTION)
	   RX_WR_1		      => local_compl_rx_wr_1,       -- Write Request 1
	   RX_ALLOW		      => local_compl_rx_allow,      -- Allow to write
	   RX_LOCAL_TAG      => local_compl_rx_local_tag,  -- Local Tag
	  -- Read Interface -------------------------------------------------------
      TX_TAG            => local_compl_tx_tag, 	      -- Transaction Tag     
      TX_REQ_ID         => local_compl_tx_req_id,     -- Requester ID (BUS, DEVICE, FUNCTION)
      TX_RD             => local_compl_tx_rd,         -- Read Request
      TX_RTAG           => local_compl_tx_rtag,	      -- Read Address
      -- Status Interface -----------------------------------------------------
      STATUS            => local_compl_status,
--       TRANS_EN_N        => local_compl_trans_en_n,    -- Enable Transactions
	   RX_FULL		      => local_compl_rx_full		   -- Local Buffer Full

   );

   -- -------------------------------------------------------------------------
   --              GLOBAL COMPLETION BUFFER                                  --
   -- -------------------------------------------------------------------------
   GLOBAL_COMPL_BUF_U : entity work.GLOBAL_COMPL_BUF
      generic map(
       GLOBAL_TAG_WIDTH 	=> GLOBAL_TAG_WIDTH         -- 'Global' Tag width  ( MUST BE <=7 )
      )  
      port map (
       -- clock & reset --------------------------------------------------------
       CLK              => trn_clk,       -- FPGA clock
       RESET            => trn_reset, 	   -- Reset active high

	    -- Read Interface -------------------------------------------------------
       RX_LOCAL_ADDR    => global_compl_rx_local_addr,-- Local Address     
       RX_LOCAL_TAG     => global_compl_rx_local_tag, -- Local Tag     
       RX_RD     	      => global_compl_rx_rd,	      -- Read Request
       RX_GLOBAL_TAG    => global_compl_rx_global_tag,-- Read Address
	    RX_LAST_CPL	   => global_compl_rx_last_cpl,  -- Last Completion
	    RX_LEN_CPL	      => global_compl_rx_len_cpl,   -- Completion Length

	    -- Write interface ------------------------------------------------------
       TX_LOCAL_ADDR    => global_compl_tx_local_addr,-- Local Address
	    TX_LOCAL_TAG     => global_compl_tx_local_tag, -- Local Tag
	    TX_WR			   => global_compl_tx_wr,			-- Write Request
       TX_ALLOW         => global_compl_tx_allow,     -- Allow to write
	    TX_RTAG 		   => global_compl_tx_rtag,      -- Global Tag

       TX_FULL          => global_compl_tx_full,      -- Global Buffer full 
       TRANS_EN_N       => global_compl_trans_en_n,   -- Trans EN 
       STATUS           => global_compl_status        -- Status 
   );
   
 
   -- -------------------------------------------------------------------------
   --              INTERNAL BUS PACKET DECODER                               --
   -- -------------------------------------------------------------------------
   IB_DECODER_U : entity work.IB_DECODER
     generic map (
       INPUT_PIPE                   => true,
       DISCARD_UNSUPPORTED_IB_TRANS => DISCARD_UNSUPPORTED_IB_TRANS
       )
     port map (
      -- PCI Express Common signals -------------------------------------------
      TRN_RESET_N    => trn_reset_n,
      TRN_CLK        => trn_clk,
    -- ----------- Internal Bus RX interface ---------------------------------
      RX_DATA        => RX_DATA,
      RX_SOP_N       => RX_SOP_N,
      RX_EOP_N       => RX_EOP_N,
      RX_SRC_RDY_N   => RX_SRC_RDY_N,
      RX_DST_RDY_N   => RX_DST_RDY_N,

    -- ----------- PCIe Generator interface ----------------------------------
      GEN_DATA       => ib_dec_out_data,            -- Data or Header
      GEN_SOP_N      => ib_dec_out_sop_n,           -- Start of Packet
      GEN_EOP_N      => ib_dec_out_eop_n,           -- End of Packet
      GEN_SRC_RDY_N  => ib_dec_out_src_rdy_n,       -- Source Ready
      GEN_DST_RDY_N  => ib_dec_out_dst_rdy_n,       -- Destination Ready
      GEN_DW4        => ib_dec_out_dw4,             -- DW4 Header  
      GEN_DW4_VLD    => ib_dec_out_dw4_vld,         -- DW4 Header VLD

    -- Local Completition Buffer Interface -----------------------------------
      LCB_TAG        => local_compl_tx_tag,	       -- Transaction Tag     
      LCB_REQ_ID     => local_compl_tx_req_id,      -- Requester ID (BUS, DEVICE, FUNCTION)
      LCB_RD         => local_compl_tx_rd, 	   	 -- Read Request
      LCB_RTAG       => local_compl_tx_rtag,        -- Read Address
  
    -- Global Completition Buffer Interface ----------------------------------
      GCB_LOCAL_ADDR => global_compl_tx_local_addr, -- Local Address
      GCB_LOCAL_TAG  => global_compl_tx_local_tag,  -- Local Tag
	   GCB_WR		   => global_compl_tx_wr,			 -- Write Request
      GCB_WR_ALLOW   => global_compl_tx_allow,      -- Allow to write
	   GCB_RTAG 	   => global_compl_tx_rtag        -- Global Tag
  );

   -- -------------------------------------------------------------------------
   --              SYSTEM BUS PACKET GENERATOR                               --
   -- -------------------------------------------------------------------------
   PCIE_TX_GENERATOR_U : entity work.PCIE_TX_GENERATOR
     port map (
      -- PCI Express Common signals -------------------------------------------
      TRN_RESET_N      => trn_reset_n,
      TRN_CLK          => trn_clk,
                                                                         
    -- ----------- PCIe Generator interface ----------------------------------
      GEN_DATA         => ib_dec_out_data,            -- Data or Header
      GEN_SOP_N        => ib_dec_out_sop_n,           -- Start of Packet
      GEN_EOP_N        => ib_dec_out_eop_n,           -- End of Packet
      GEN_SRC_RDY_N    => ib_dec_out_src_rdy_n,       -- Source Ready
      GEN_DST_RDY_N    => ib_dec_out_dst_rdy_n,       -- Destination Ready
      GEN_DW4          => ib_dec_out_dw4,             -- DW4 Header  
      GEN_DW4_VLD      => ib_dec_out_dw4_vld,         -- DW4 Header VLD

    -- PCI Express TX interface ---------------------------------------------
      TRN_LNK_UP_N     => trn_lnk_up_n,   -- Transaction Link Up
      TRN_TD           => trn_td,         -- Transmit Data
      TRN_TREM_N       => trn_trem_n,     -- Transmit Data Reminder
      TRN_TSOF_N       => trn_tsof_n,     -- Transmit SOF
      TRN_TEOF_N       => trn_teof_n,     -- Transmit EOF
      TRN_TSRC_RDY_N   => trn_tsrc_rdy_n, -- Trnasmit Source Ready
      TRN_TDST_RDY_N   => trn_tdst_rdy_n, -- Transmit Destination Ready
      TRN_TBUF_AV      => trn_tbuf_av,    -- Transmit Buffers Available
                                          -- trn_tbuf_av[0] => Non Posted Queue
                                          -- trn_tbuf_av[1] => Posted Queue
                                          -- trn_tbuf_av[2] => Completion Queue
    -- PCI Express Configuration interface ----------------------------------
      CFG_BUS_NUMBER        => cfg_bus_number,      -- Bus number
      CFG_DEVICE_NUMBER     => cfg_device_number,   -- Device Number
      CFG_FUNCTION_NUMBER   => cfg_function_number, -- Function number
      CFG_DCOMMAND          => cfg_dcommand         -- cfg_dcommand[14:12] - Max_Read_Request_Size
                                                    -- cfg_dcommand[11]    - Enable No Snoop
                                                    -- cfg_dcommand[8]     - Extended Tag Field Enable
                                                    -- cfg_dcommand[7:5]   - Max_Payload_Size
                                                    -- cfg_dcommand[4]     - Enable Relaxed Ordering
  );

end architecture pcie2ib_bridge_arch;


