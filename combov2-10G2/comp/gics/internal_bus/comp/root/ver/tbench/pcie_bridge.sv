//
// pcie2ib_bridge.sv: System Verilog wrapper for pcie2ib bridge
// Copyright (C) 2007 CESNET
// Author(s): Tomas Malek <tomalek@liberouter.org>
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in
//    the documentation and/or other materials provided with the
//    distribution.
// 3. Neither the name of the Company nor the names of its contributors
//    may be used to endorse or promote products derived from this
//    software without specific prior written permission.
//
// This software is provided ``as is'', and any express or implied
// warranties, including, but not limited to, the implied warranties of
// merchantability and fitness for a particular purpose are disclaimed.
// In no event shall the company or contributors be liable for any
// direct, indirect, incidental, special, exemplary, or consequential
// damages (including, but not limited to, procurement of substitute
// goods or services; loss of use, data, or profits; or business
// interruption) however caused and on any theory of liability, whether
// in contract, strict liability, or tort (including negligence or
// otherwise) arising in any way out of the use of this software, even
// if advised of the possibility of such damage.
//
// $Id: pcie_bridge.sv 3629 2008-07-16 21:52:15Z xkobie00 $
//

module PCIE2IB_BRIDGE_SV (
   input logic         CLK,
   input logic         RESET,
   iPcieRx.dut         RX,
   iPcieTx.dut         TX,
   iPcieCfg.dut        CFG,
   iInternalBusTx.dut  IB_DOWN,
   iInternalBusRx.dut  IB_UP
   );

   logic RESET_N;
   assign RESET_N = ~RESET;

   PCIE2IB_BRIDGE PCIE2IB_BRIDGE_U (
      .TRN_CLK     (CLK),
      .TRN_RESET_N (RESET_N),

       // -- PCI Express TLP RX Interface
      .TRN_RBAR_HIT_N(RX.BAR_HIT_N),
      .TRN_RSOF_N(RX.SOF_N),      
      .TRN_REOF_N(RX.EOF_N),    
      .TRN_RD(RX.DATA),         
      .TRN_RREM_N(RX.REM_N),       
      .TRN_RSRC_RDY_N(RX.SRC_RDY_N), 
      .TRN_RDST_RDY_N(RX.DST_RDY_N),
      .TRN_RERRFWD_N(RX.ERR_FWD_N),   
      .TRN_RNP_OK_N(RX.NP_OK_N),         
      .TRN_RCPL_STREAMING_N(RX.CPL_STREAMING_N),
      .TRN_RSRC_DSC_N(RX.SRC_DSC_N),
      .TRN_RFC_PD_AV(RX.FC_PD_AV),
      .TRN_RFC_NPD_AV(RX.FC_NPD_AV),
      .TRN_RFC_NPH_AV(RX.FC_NPH_AV),
      .TRN_RFC_PH_AV(RX.FC_PH_AV),

      // -- PCI Express TLP TX Interface
      .TRN_LNK_UP_N(TX.LNK_UP_N),
      .TRN_TD(TX.TD),
      .TRN_TREM_N(TX.REM_N),
      .TRN_TSOF_N(TX.SOF_N),
      .TRN_TEOF_N(TX.EOF_N),
      .TRN_TSRC_RDY_N(TX.SRC_RDY_N),
      .TRN_TDST_RDY_N(TX.DST_RDY_N),
      .TRN_TSRC_DSC_N(TX.SRC_DSC_N),
      .TRN_TERRFWD_N(TX.ERRFWD_N),
      .TRN_TDST_DSC_N(TX.DST_DSC_N),
      .TRN_TBUF_AV(TX.BUF_AV),

       // -- PCI Express Host Configuration Interface
      .CFG_DO(CFG.DO),
      .CFG_RD_WR_DONE_N(CFG.RD_WR_DONE_N),
      .CFG_DI(CFG.DI),
      .CFG_DWADDR(CFG.DWADDR),
      .CFG_WR_EN_N(CFG.WR_EN_N),
      .CFG_RD_EN_N(CFG.RD_EN_N),
      .CFG_INTERRUPT_N(CFG.INTERRUPT_N),
      .CFG_INTERRUPT_RDY_N(CFG.INTERRUPT_RDY_N),
      .CFG_INTERRUPT_MMENABLE(CFG.INTERRUPT_MMENABLE),
      .CFG_INTERRUPT_MSIENABLE(CFG.INTERRUPT_MSIENABLE),
      .CFG_INTERRUPT_DI(CFG.INTERRUPT_DI),
      .CFG_INTERRUPT_DO(CFG.INTERRUPT_DO),
      .CFG_INTERRUPT_ASSERT_N(CFG.INTERRUPT_ASSERT_N),
      .CFG_TO_TURNOFF_N(CFG.TO_TURNOFF_N),
      .CFG_BYTE_EN_N(CFG.BYTE_EN_N),
      .CFG_BUS_NUMBER(CFG.BUS_NUMBER),
      .CFG_DEVICE_NUMBER(CFG.DEVICE_NUMBER),
      .CFG_FUNCTION_NUMBER(CFG.FUNCTION_NUMBER),
      .CFG_STATUS(CFG.STATUS),
      .CFG_COMMAND(CFG.COMMAND),
      .CFG_DSTATUS(CFG.DSTATUS),
      .CFG_DCOMMAND(CFG.DCOMMAND),
      .CFG_LSTATUS(CFG.LSTATUS),
      .CFG_LCOMMAND(CFG.LCOMMAND),
      .CFG_PM_WAKE_N(CFG.PM_WAKE_N),
      .CFG_PCIE_LINK_STATE_N(CFG.PCIE_LINK_STATE_N),
      .CFG_TRN_PENDING_N(CFG.TRN_PENDING_N),
      .CFG_DSN(CFG.DSN),
      .CFG_ERR_ECRC_N(CFG.ERR_ECRC_N),
      .CFG_ERR_UR_N(CFG.ERR_UR_N),
      .CFG_ERR_CPL_TIMEOUT_N(CFG.ERR_CPL_TIMEOUT_N),
      .CFG_ERR_CPL_UNEXPECT_N(CFG.ERR_CPL_UNEXPECT_N),
      .CFG_ERR_CPL_ABORT_N(CFG.ERR_CPL_ABORT_N),
      .CFG_ERR_POSTED_N(CFG.ERR_POSTED_N),
      .CFG_ERR_COR_N(CFG.ERR_COR_N),
      .CFG_ERR_TLP_CPL_HEADER(CFG.ERR_TLP_CPL_HEADER),
      .CFG_ERR_CPL_RDY_N(CFG.ERR_CPL_RDY_N),
      
      // -- Internal Bus TX interface
      .TX_DATA(IB_DOWN.DATA),             
      .TX_SOP_N(IB_DOWN.SOP_N), 
      .TX_EOP_N(IB_DOWN.EOP_N),
      .TX_SRC_RDY_N(IB_DOWN.SRC_RDY_N),
      .TX_DST_RDY_N(IB_DOWN.DST_RDY_N),

      // -- Internal Bus RX interface
      .RX_DATA(IB_UP.DATA),             
      .RX_SOP_N(IB_UP.SOP_N), 
      .RX_EOP_N(IB_UP.EOP_N),
      .RX_SRC_RDY_N(IB_UP.SRC_RDY_N),
      .RX_DST_RDY_N(IB_UP.DST_RDY_N)
   );

endmodule



