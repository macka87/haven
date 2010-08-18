//
// SystemVerilog Wrapper For IB_ENDPOINT_MASTER
//

module IB_ENDPOINT_MASTER (
   input logic CLK,
   input logic RESET,
   iIbEndpointWrite64.endpoint WR,
   iIbEndpointRead64s.endpoint RD,
   iIbEndpointMaster.endpoint BM,
   iInternalBusLink.rx IB_DOWN,
   iInternalBusLink.tx IB_UP);

   IB_ENDPOINT_MASTER_NOREC IB_ENDPOINT_MASTER_INST (
      .IB_CLK         (CLK),
      .IB_RESET       (RESET),

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

      .WR_ADDR(WR.ADDR),
      .WR_DATA(WR.DATA),
      .WR_BE(WR.BE),
      .WR_REQ(WR.REQ),
      .WR_RDY(WR.RDY),
      .WR_LENGTH(WR.LENGTH),
      .WR_SOF(WR.SOF),
      .WR_EOF(WR.EOF),

      .RD_ADDR(RD.ADDR),
      .RD_BE(RD.BE),
      .RD_REQ(RD.REQ),
      .RD_ARDY(RD.ARDY),
      .RD_SOF_IN(RD.SOF_IN),
      .RD_EOF_IN(RD.EOF_IN),
      .RD_DATA(RD.DATA),
      .RD_SRC_RDY(RD.SRC_RDY),
      .RD_DST_RDY(RD.DST_RDY),

      .BM_GLOBAL_ADDR(BM.GLOBAL_ADDR),  
      .BM_LOCAL_ADDR(BM.LOCAL_ADDR),   
      .BM_LENGTH(BM.LENGTH),  
      .BM_TAG(BM.TAG),          
      .BM_TRANS_TYPE(BM.TRANS_TYPE),   
      .BM_REQ(BM.REQ),          
      .BM_ACK(BM.ACK),          
      .BM_OP_TAG(BM.OP_TAG),       
      .BM_OP_DONE(BM.OP_DONE)      
   );

endmodule
