--
-- pcie2ib_bridge_arch.vhd : PCIe to IB Bridge architecture
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

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

library unisim;
use unisim.vcomponents.all;

-- ----------------------------------------------------------------------------
--               ARCHITECTURE DECLARATION  --  PCIe to IB Bridge             --
-- ----------------------------------------------------------------------------

architecture pcie_bridge_arch of PCIE2IB_BRIDGE is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   -- RX buffer <-> Completion buffer interface -------------------------------
   -- Write LR_BUF ifc
   signal rxcompl_tc          : std_logic_vector(2 downto 0);
   signal rxcompl_attr        : std_logic_vector(1 downto 0);
   signal rxcompl_tag         : std_logic_vector(7 downto 0);
   signal rxcompl_bus_num     : std_logic_vector(7 downto 0);
   signal rxcompl_device_num  : std_logic_vector(4 downto 0);
   signal rxcompl_func_num    : std_logic_vector(2 downto 0);
   signal rxcompl_bmaddr      : std_logic_vector(63 downto 0);
   signal rxcompl_full        : std_logic;

   signal rxcompl_we          : std_logic;
   signal rxcompl_wtag        : std_logic_vector(LTAG_WIDTH-1 downto 0);

   -- Read GR_BUF ifc
   signal rxcompl_graddr_in   : std_logic_vector(31 downto 0);
   signal rxcompl_grtag_in    : std_logic_vector(15 downto 0);
   signal rxcompl_write       : std_logic;

   signal rxcompl_graddr_out  : std_logic_vector(31 downto 0);
   signal rxcompl_grtag_out   : std_logic_vector(15 downto 0);
   signal rxcompl_rd          : std_logic;
   signal rxcompl_rtag        : std_logic_vector(GTAG_WIDTH-1 downto 0);
   signal rxcompl_vld         : std_logic;

   signal rxcompl_last        : std_logic;

   -- TX buffer <-> Completion buffer interface -------------------------------
   -- Read LR_BUF ifc
   signal txcompl_tc          : std_logic_vector(2 downto 0);
   signal txcompl_attr        : std_logic_vector(1 downto 0);
   signal txcompl_tag         : std_logic_vector(7 downto 0);
   signal txcompl_bus_num     : std_logic_vector(7 downto 0);
   signal txcompl_device_num  : std_logic_vector(4 downto 0);
   signal txcompl_func_num    : std_logic_vector(2 downto 0);
   signal txcompl_bmaddr      : std_logic_vector(63 downto 0);

   signal txcompl_rd          : std_logic;
   signal txcompl_rtag        : std_logic_vector(LTAG_WIDTH-1 downto 0);
   signal txcompl_vld         : std_logic;

   -- Write GR_BUF ifc
   signal txcompl_graddr      : std_logic_vector(31 downto 0);
   signal txcompl_grtag       : std_logic_vector(15 downto 0);
   signal txcompl_we          : std_logic;
   signal txcompl_wtag        : std_logic_vector(GTAG_WIDTH-1 downto 0);
   signal txcompl_full        : std_logic;

   -- TRANS buffer <--> TLP generator interface -------------------------------
   signal tlptx_req          : std_logic;
   signal tlptx_ack          : std_logic;
   signal tlptx_wait         : std_logic;
   signal tlptx_data         : std_logic_vector(63 downto 0);
   signal tlptx_dwe          : std_logic_vector( 1 downto 0);

   signal tlptx_chtc         : std_logic_vector(2 downto 0);
   signal tlptx_chfifo       : std_logic_vector(1 downto 0);
   signal tlptx_srcrdy_n     : std_logic;

   -- TRANS buffer <--> TLP decoder interface ---------------------------------
   signal tlprx_req          : std_logic;
   signal tlprx_ack          : std_logic;
   signal tlprx_ready        : std_logic;
   signal tlprx_core         : std_logic;
   signal tlprx_wait         : std_logic;
   signal tlprx_idle         : std_logic;
   signal tlprx_readback     : std_logic;
   signal tlprx_full         : std_logic;
   signal tlprx_barbase      : std_logic_vector(31 downto 0);
   signal tlprx_barmask      : std_logic_vector(31 downto 0);
   signal tlprx_data         : std_logic_vector(63 downto 0);
   signal tlprx_dwe          : std_logic_vector( 1 downto 0);

   -- BUS MASTER buffer interface signals -------------------------------------
   signal b_m_global_addr     : std_logic_vector(63 downto 0);
   signal b_m_local_addr      : std_logic_vector(31 downto 0);
   signal b_m_length          : std_logic_vector(11 downto 0);
   signal b_m_tag             : std_logic_vector(15 downto 0);
   signal b_m_req_r           : std_logic;
   signal b_m_req_w           : std_logic;
   signal b_m_ack_r           : std_logic;
   signal b_m_ack_w           : std_logic;
   signal b_m_full_r          : std_logic;
   signal b_m_full_w          : std_logic;
   signal b_m_op_tag_r        : std_logic_vector(15 downto 0);
   signal b_m_op_tag_w        : std_logic_vector(15 downto 0);
   signal b_m_op_done_r       : std_logic;
   signal b_m_op_done_w       : std_logic;
   
begin

   -- -------------------------------------------------------------------------
   --                               RX BUFFER                                --
   -- -------------------------------------------------------------------------

   U_rx_buf: entity work.RX_BUF
      generic map(
         IB_BASE_ADDR  => IB_BASE_ADDR,
         LTAG_WIDTH    => LTAG_WIDTH,
         GTAG_WIDTH    => GTAG_WIDTH
      )
      port map(
         CLK          => CLK,
         RESET        => RESET,

         -- PCI Express RX interface --
         TLPRX_REQ      => tlprx_req,
         TLPRX_ACK      => tlprx_ack,
         TLPRX_WAIT     => tlprx_wait,
         TLPRX_READY    => tlprx_ready,
         TLPRX_CORE     => tlprx_core,
         TLPRX_IDLE     => tlprx_idle,
         TLPRX_READBACK => tlprx_readback,
         TLPRX_BARBASE  => tlprx_barbase,
         TLPRX_BARMASK  => tlprx_barmask,
         TLPRX_FULL     => tlprx_full,

         TLPRX_DATA   => tlprx_data,
         TLPRX_DWE    => tlprx_dwe,

         -- Internal Bus interface --
         IB_DOWN_DATA       => IB.DOWN.DATA,
         IB_DOWN_SOP_N      => IB.DOWN.SOP_N,
         IB_DOWN_EOP_N      => IB.DOWN.EOP_N,
         IB_DOWN_SRC_RDY_N  => IB.DOWN.SRC_RDY_N,
         IB_DOWN_DST_RDY_N  => IB.DOWN.DST_RDY_N,

         -- Completion Buffer interface --
         -- Write LR_BUF ifc
         RXTC         => rxcompl_tc,
         RXATTR       => rxcompl_attr,
         RXTAG        => rxcompl_tag,
         RXBUS_NUM    => rxcompl_bus_num,
         RXDEVICE_NUM => rxcompl_device_num,
         RXFUNC_NUM   => rxcompl_func_num,
         RXBMADDR     => rxcompl_bmaddr,

         RXWE         => rxcompl_we,
         RXWTAG       => rxcompl_wtag,

         RXFULL       => rxcompl_full,

         -- Read GR_BUF ifc
         RXGRADDR_IN  => rxcompl_graddr_in,
         RXGRTAG_IN   => rxcompl_grtag_in,
         RXWRITE      => rxcompl_write,

         RXGRADDR_OUT => rxcompl_graddr_out,
         RXGRTAG_OUT  => rxcompl_grtag_out,
         RXRD         => rxcompl_rd,
         RXRTAG       => rxcompl_rtag,
         RXVLD        => rxcompl_vld,

         RXLAST       => rxcompl_last,

         -- Bus Master Buffer interface --
         BM_GLOBAL_ADDR  => b_m_global_addr,
         BM_LOCAL_ADDR   => b_m_local_addr,
         BM_LENGTH       => b_m_length,
         BM_TAG          => b_m_tag,

         BM_REQ_W        => b_m_req_w,
         BM_ACK_W        => b_m_ack_w,
         BM_FULL_W       => b_m_full_w,

         BM_OP_TAG_R     => b_m_op_tag_r,
         BM_OP_DONE_R    => b_m_op_done_r
      );

   -- -------------------------------------------------------------------------
   --                           COMPLETION BUFFER                            --
   -- -------------------------------------------------------------------------

   U_compl_buf: entity work.COMPL_BUF
      generic map(
         LTAG_WIDTH => LTAG_WIDTH,
         GTAG_WIDTH => GTAG_WIDTH
      )
      port map(
         CLK           => CLK,
         RESET         => RESET,

         -- 'Local Read' Buffer (LR_BUF) interface -------------------------------
         -- RX buffer part (write ifc) --
         RX_TC         => rxcompl_tc,
         RX_ATTR       => rxcompl_attr,
         RX_TAG        => rxcompl_tag,
         RX_BUS_NUM    => rxcompl_bus_num,
         RX_DEVICE_NUM => rxcompl_device_num,
         RX_FUNC_NUM   => rxcompl_func_num,
         RX_BMADDR     => rxcompl_bmaddr,

         RXWE          => rxcompl_we,
         RXWTAG        => rxcompl_wtag,

         RX_FULL       => rxcompl_full,

         -- TX buffer part (read ifc) --
         TX_TC         => txcompl_tc,
         TX_ATTR       => txcompl_attr,
         TX_TAG        => txcompl_tag,
         TX_BUS_NUM    => txcompl_bus_num,
         TX_DEVICE_NUM => txcompl_device_num,
         TX_FUNC_NUM   => txcompl_func_num,
         TX_BMADDR     => txcompl_bmaddr,

         TXRD          => txcompl_rd,
         TXRTAG        => txcompl_rtag,
         TXVLD         => txcompl_vld,

         -- 'Global Read' Buffer (GR_BUF) interface ------------------------------
         -- RX buffer part (read ifc) --
         RX_GRADDR_IN  => rxcompl_graddr_in,
         RX_GRTAG_IN   => rxcompl_grtag_in,
         RX_WRITE      => rxcompl_write,

         RX_GRADDR_OUT => rxcompl_graddr_out,
         RX_GRTAG_OUT  => rxcompl_grtag_out,
         RXRD          => rxcompl_rd,
         RXRTAG        => rxcompl_rtag,
         RXVLD         => rxcompl_vld,

         RXLAST        => rxcompl_last,

         -- TX buffer part (write ifc) --
         TX_GRADDR    => txcompl_graddr,
         TX_GRTAG     => txcompl_grtag,

         TXWE         => txcompl_we,
         TXWTAG       => txcompl_wtag,
         TX_FULL      => txcompl_full
      );

   -- -------------------------------------------------------------------------
   --                               TX BUFFER                                --
   -- -------------------------------------------------------------------------

   U_tx_buf: entity work.TX_BUF
      generic map(
         LTAG_WIDTH  => LTAG_WIDTH,
         GTAG_WIDTH  => GTAG_WIDTH
      )
      port map(
         -- clock & reset --------------------------------------------------------
         CLK             => CLK,
         RESET           => RESET,

         -- PCI Express TX interface ---------------------------------------------
         TLPTX_REQ       => tlptx_req,
         TLPTX_ACK       => tlptx_ack,
         TLPTX_WAIT      => tlptx_wait,

         TLPTX_DATA      => tlptx_data,
         TLPTX_DWE       => tlptx_dwe,

         -- Internal Bus UP interface --------------------------------------------
         IB_UP_DATA      => IB.UP.DATA,
         IB_UP_SOP_N     => IB.UP.SOP_N,
         IB_UP_EOP_N     => IB.UP.EOP_N,
         IB_UP_SRC_RDY_N => IB.UP.SRC_RDY_N,
         IB_UP_DST_RDY_N => IB.UP.DST_RDY_N,

         -- Completion Buffer interface ------------------------------------------
         -- Read LR Buffer ifc --
         TXTC            => txcompl_tc,
         TXATTR          => txcompl_attr,
         TXTAG           => txcompl_tag,
         TXBUS_NUM       => txcompl_bus_num,
         TXDEVICE_NUM    => txcompl_device_num,
         TXFUNC_NUM      => txcompl_func_num,
         TXBMADDR        => txcompl_bmaddr,

         TXRD            => txcompl_rd,
         TXRTAG          => txcompl_rtag,
         TXVLD           => txcompl_vld,

         -- Write GR Buffer ifc --
         TXGRADDR        => txcompl_graddr,
         TXGRTAG         => txcompl_grtag,

         TXWE            => txcompl_we,
         TXWTAG          => txcompl_wtag,
         TXFULL          => txcompl_full,

         -- Bus Master Buffer interface ---------------------------------------
         BM_GLOBAL_ADDR  => b_m_global_addr,
         BM_LOCAL_ADDR   => b_m_local_addr,
         BM_LENGTH       => b_m_length,
         BM_TAG          => b_m_tag,

         BM_REQ_R        => b_m_req_r,
         BM_ACK_R        => b_m_ack_r,
         BM_FULL_R       => b_m_full_r,

         BM_OP_TAG_W     => b_m_op_tag_w,
         BM_OP_DONE_W    => b_m_op_done_w,

         -- Configuration interface -------------------------------------------
         BUS_NUM         => CFG.BUS_NUM,
         DEVICE_NUM      => CFG.DEVICE_NUM,
         FUNC_NUM        => CFG.FUNC_NUM,
         MAX_PAYLOAD_SIZE=> CFG.MAX_PAYLOAD_SIZE
      );

   -- -------------------------------------------------------------------------
   --     'PCIe Endpoint Block to TLP DEC/GEN' TRANSFORMATION BUFFER         --
   -- -------------------------------------------------------------------------

   U_trans_buf: entity work.TRANS_BUF
      generic map(
         BAR_HIT_MASK    => BAR_HIT_MASK,
         BAR0_BASE       => BAR0_BASE,
         BAR1_BASE       => BAR1_BASE,
         BAR2_BASE       => BAR2_BASE,
         BAR3_BASE       => BAR3_BASE,
         BAR4_BASE       => BAR4_BASE,
         BAR5_BASE       => BAR5_BASE,
         BAR6_BASE       => BAR6_BASE,
         BAR0_MASK       => BAR0_MASK,
         BAR1_MASK       => BAR1_MASK,
         BAR2_MASK       => BAR2_MASK,
         BAR3_MASK       => BAR3_MASK,
         BAR4_MASK       => BAR4_MASK,
         BAR5_MASK       => BAR5_MASK,
         BAR6_MASK       => BAR6_MASK
      )
      port map(
         -- clock & reset --------------------------------------------------------
         CLK              => CLK,
         RESET            => RESET,

         -- PCI Express Transaction Layer interface ------------------------------
         -- RX link --
         PCIERX_SOF_N     => PCIE.RX.SOF_N,
         PCIERX_EOF_N     => PCIE.RX.EOF_N,
         PCIERX_DATA      => PCIE.RX.DATA,
         PCIERX_REM_N     => PCIE.RX.REM_N,
         PCIERX_SRC_RDY_N => PCIE.RX.SRC_RDY_N,
         PCIERX_DST_RDY_N => PCIE.RX.DST_RDY_N,
         PCIERX_SRC_DSC_N => PCIE.RX.SRC_DSC_N,
         PCIERX_ERR_FWD_N => PCIE.RX.ERR_FWD_N,
         PCIERX_NP_OK_N   => PCIE.RX.NP_OK_N,
         PCIERX_BAR_HIT_N => PCIE.RX.BAR_HIT_N,
         PCIERX_FC_PH_AV  => PCIE.RX.FC_PH_AV,
         PCIERX_FC_PD_AV  => PCIE.RX.FC_PD_AV,
         PCIERX_FC_NPH_AV => PCIE.RX.FC_NPH_AV,
         PCIERX_FC_NPD_AV => PCIE.RX.FC_NPD_AV,

         -- TX link --
         PCIETX_SOF_N     => PCIE.TX.SOF_N,
         PCIETX_EOF_N     => PCIE.TX.EOF_N,
         PCIETX_DATA      => PCIE.TX.DATA,
         PCIETX_REM_N     => PCIE.TX.REM_N,
         PCIETX_SRC_RDY_N => PCIE.TX.SRC_RDY_N,
         PCIETX_DST_RDY_N => PCIE.TX.DST_RDY_N,
         PCIETX_SRC_DSC_N => PCIE.TX.SRC_DSC_N,
         PCIETX_DST_DCS_N => PCIE.TX.DST_DCS_N,
         PCIETX_BUF_AV    => PCIE.TX.BUF_AV,

         -- TLP generator/decoder interface --------------------------------------
         -- Decoder --
         TLPRX_REQ        => tlprx_req,   --
         TLPRX_ACK        => tlprx_ack,   --
         TLPRX_WAIT       => tlprx_wait,  --
         TLPRX_READY      => tlprx_ready, --
         TLPRX_CORE       => tlprx_core,
         TLPRX_IDLE       => tlprx_idle,
         TLPRX_READBACK   => tlprx_readback,
         TLPRX_BARBASE    => tlprx_barbase,
         TLPRX_BARMASK    => tlprx_barmask,
         TLPRX_FULL       => tlprx_full, 

         TLPRX_DATA       => tlprx_data,  --
         TLPRX_DWE        => tlprx_dwe,

         -- Generator --
         TLPTX_REQ        => tlptx_req,
         TLPTX_ACK        => tlptx_ack,
         TLPTX_WAIT       => tlptx_wait,

         TLPTX_DATA       => tlptx_data,
         TLPTX_DWE        => tlptx_dwe
      );

   -- -------------------------------------------------------------------------
   --                          BUS MASTER BUFFER                             --
   -- -------------------------------------------------------------------------

   U_bm_buf: entity work.BM_BUF
      port map (
         -- clock & reset --------------------------------------------------------
         CLK            => CLK,
         RESET          => RESET,

         -- Bus Master interface -------------------------------------------------
         BM             => BM,

         -- TX and RX Buffer interface -------------------------------------------
         -- Output --
         B_M_GLOBAL_ADDR => b_m_global_addr,
         B_M_LOCAL_ADDR  => b_m_local_addr,
         B_M_LENGTH      => b_m_length,
         B_M_TAG         => b_m_tag,

         B_M_REQ_R       => b_m_req_r,
         B_M_REQ_W       => b_m_req_w,

         -- Input --
         B_M_ACK_R       => b_m_ack_r,
         B_M_ACK_W       => b_m_ack_w,

         B_M_FULL_R      => b_m_full_r,
         B_M_FULL_W      => b_m_full_w,

         B_M_OP_TAG_R    => b_m_op_tag_r,
         B_M_OP_TAG_W    => b_m_op_tag_w,

         B_M_OP_DONE_R   => b_m_op_done_r,
         B_M_OP_DONE_W   => b_m_op_done_w
      );
      
end pcie_bridge_arch;
