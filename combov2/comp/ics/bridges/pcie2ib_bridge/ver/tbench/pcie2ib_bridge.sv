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
// $Id: pcie2ib_bridge.sv 688 2007-10-19 16:11:56Z tomalek $
//

module PCIE2IB_BRIDGE_SV (
   input logic CLK,
   input logic RESET,
   iPcieRx.bridge      RX,
   iPcieTx.bridge      TX,
   iPcieCfg.bridge     CFG,
   iIbBm64.comp        BM,
   iInternalBusLink.tx IB_DOWN,
   iInternalBusLink.rx IB_UP);

   PCIE2IB_BRIDGE_NOREC PCIE2IB_BRIDGE_INST (
      .CLK         (CLK),
      .RESET       (RESET),

      .PCIERX_SOF_N(RX.SOF_N),     
      .PCIERX_EOF_N(RX.EOF_N),                  
      .PCIERX_DATA(RX.DATA),      
      .PCIERX_REM_N(RX.REM_N),                 
      .PCIERX_SRC_RDY_N(RX.SRC_RDY_N), 
      .PCIERX_DST_RDY_N(RX.DST_RDY_N),   
      .PCIERX_SRC_DSC_N(RX.SRC_DSC_N), 
      .PCIERX_ERR_FWD_N(RX.ERR_FWD_N), 
      .PCIERX_NP_OK_N(RX.NP_OK_N),                                                                                                                                            
      .PCIERX_BAR_HIT_N(RX.BAR_HIT_N),                                                                                                                                          
      .PCIERX_FC_PH_AV(RX.FC_PH_AV),  
      .PCIERX_FC_PD_AV(RX.FC_PD_AV),  
      .PCIERX_FC_NPH_AV(RX.FC_NPH_AV), 
      .PCIERX_FC_NPD_AV(RX.FC_NPD_AV), 

      .PCIETX_SOF_N(TX.SOF_N),     
      .PCIETX_EOF_N(TX.EOF_N),                  
      .PCIETX_DATA(TX.DATA),      
      .PCIETX_REM_N(TX.REM_N),                  
      .PCIETX_SRC_RDY_N(TX.SRC_RDY_N), 
      .PCIETX_DST_RDY_N(TX.DST_RDY_N),
      .PCIETX_SRC_DSC_N(TX.SRC_DCS_N), 
      .PCIETX_DST_DCS_N(TX.DST_DCS_N),                                          
      .PCIETX_BUF_AV(TX.BUF_AV),    

      .IB_UP_DATA      (IB_UP.DATA),
      .IB_UP_SOP_N     (IB_UP.SOP_N),
      .IB_UP_EOP_N     (IB_UP.EOP_N),
      .IB_UP_SRC_RDY_N (IB_UP.SRC_RDY_N),
      .IB_UP_DST_RDY_N (IB_UP.DST_RDY_N),

      .IB_DOWN_DATA    (IB_DOWN.DATA),
      .IB_DOWN_SOP_N   (IB_DOWN.SOP_N),
      .IB_DOWN_EOP_N   (IB_DOWN.EOP_N),
      .IB_DOWN_SRC_RDY_N(IB_DOWN.SRC_RDY_N),
      .IB_DOWN_DST_RDY_N(IB_DOWN.DST_RDY_N),

      .BM_GLOBAL_ADDR(BM.GLOBAL_ADDR),  
      .BM_LOCAL_ADDR(BM.LOCAL_ADDR),   
      .BM_LENGTH(BM.LENGTH),  
      .BM_TAG(BM.TAG),          
      .BM_TRANS_TYPE(BM.TRANS_TYPE),   
      .BM_REQ(BM.REQ),          
      .BM_ACK(BM.ACK),          
      .BM_OP_TAG(BM.OP_TAG),       
      .BM_OP_DONE(BM.OP_DONE),

      .CFG_BUS_NUM(CFG.BUS_NUM),
      .CFG_DEVICE_NUM(CFG.DEVICE_NUM),       
      .CFG_FUNC_NUM(CFG.FUNC_NUM),         
      .CFG_MAX_PAYLOAD_SIZE(CFG.MAX_PAYLOAD_SIZE) 
   );

endmodule



