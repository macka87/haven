/*
 * DUT.sv: Design under test
 * Copyright (C) 2008 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 * 3. Neither the name of the Company nor the names of its contributors
 *    may be used to endorse or promote products derived from this
 *    software without specific prior written permission.
 *
 * This software is provided ``as is'', and any express or implied
 * warranties, including, but not limited to, the implied warranties of
 * merchantability and fitness for a particular purpose are disclaimed.
 * In no event shall the company or contributors be liable for any
 * direct, indirect, incidental, special, exemplary, or consequential
 * damages (including, but not limited to, procurement of substitute
 * goods or services; loss of use, data, or profits; or business
 * interruption) however caused and on any theory of liability, whether
 * in contract, strict liability, or tort (including negligence or
 * otherwise) arising in any way out of the use of this software, even
 * if advised of the possibility of such damage.
 *
 * $Id: dut.sv 9148 2009-07-06 08:01:21Z xsanta06 $
 *
 * TODO:
 *
 */
 
// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module DUT (
   input logic            CLK,
   input logic            RESET,
   iInternalBus.ib_write  IB,
   iPacDmaCtrl.misc       MISC,
   iPacDmaCtrl.descriptor DESC,
   iPacDmaCtrl.statustx   SU,
   iDmaCtrl.dma           DMA,
   iFrameLinkTx.dut       FL[FLOWS]
);

// Signals for DUT conection
// FrameLink Interface
wire [BUFFER_DATA_WIDTH-1:0]  fl_data;  
wire [FLOWS-1:0]  fl_sop_n;
wire [FLOWS-1:0]  fl_eop_n;
wire [FLOWS-1:0]  fl_sof_n;
wire [FLOWS-1:0]  fl_eof_n;
wire [TXDREMWIDTH*FLOWS-1:0]  fl_rem;
wire [FLOWS-1:0]  fl_src_rdy_n;
wire [FLOWS-1:0]  fl_dst_rdy_n;

// Connecting FR to interfaces
generate
for (genvar i=0; i<FLOWS; i++) begin
  assign FL[i].DATA      = fl_data[(i+1)*TXDWIDTH-1:TXDWIDTH*i];
  assign FL[i].SOP_N     = fl_sop_n[i];
  assign FL[i].EOP_N     = fl_eop_n[i];
  assign FL[i].SOF_N     = fl_sof_n[i];
  assign FL[i].EOF_N     = fl_eof_n[i];
  assign FL[i].DREM      = fl_rem[(i+1)*TXDREMWIDTH-1:TXDREMWIDTH*i];
  assign FL[i].SRC_RDY_N = fl_src_rdy_n[i];
  assign fl_dst_rdy_n[i] = FL[i].DST_RDY_N;
end
endgenerate

// -------------------- Module body -------------------------------------------
tx_ctrl_buf_pac #(
        .FLOWS                   (FLOWS),
        .BUFFER_DATA_WIDTH       (BUFFER_DATA_WIDTH),
        .BUFFER_BLOCK_SIZE       (BUFFER_BLOCK_SIZE),
        .BUFFER_TOTAL_FLOW_SIZE  (BUFFER_TOTAL_FLOW_SIZE),
        .CTRL_BUFFER_ADDR        (CTRL_BUFFER_ADDR),      
        .CTRL_BUFFER_GAP         (CTRL_BUFFER_GAP),       
        .CTRL_BUFFER_SIZE        (CTRL_BUFFER_SIZE),      
        .CTRL_DMA_ID             (CTRL_DMA_ID),           
        .CTRL_DMA_DATA_WIDTH     (CTRL_DMA_DATA_WIDTH),   
        .CTRL_BLOCK_SIZE         (CTRL_BLOCK_SIZE)       
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK            (CLK),
     .RESET          (RESET),
    
    // Misc signals 
     .RUN            (MISC.RUN),
     .IDLE           (MISC.IDLE),         
 
    // Descriptor FIFO interface
     .DESC_READ      (DESC.DESC_READ),
     .DESC_ADDR      (DESC.DESC_ADDR),
     .DESC_DO        (DESC.DESC_DO),
     .DESC_DO_VLD    (DESC.DESC_DO_VLD),
     .DESC_EMPTY     (DESC.DESC_EMPTY),
     
    // DMA Interface 
     .DMA_ADDR       (DMA.DMA_ADDR),
     .DMA_DOUT       (DMA.DMA_DOUT),
     .DMA_REQ        (DMA.DMA_REQ),
     .DMA_ACK        (DMA.DMA_ACK),
     .DMA_DONE       (DMA.DMA_DONE),
     .DMA_TAG        (DMA.DMA_TAG),
     
    // Status update interface
     .SU_ADDR        (SU.SU_ADDR),
     .SU_DATA        (SU.SU_DATA_TX),
     .SU_DATA_VLD    (SU.SU_DATA_VLD),
     .SU_HFULL       (SU.SU_HFULL),
    
    // Write interface (InternalBus)
     .WR_ADDR        (IB.WR_ADDR),
     .WR_BE          (IB.WR_BE),
     .WR_REQ         (IB.WR_REQ),
     .WR_RDY         (IB.WR_RDY),
     .WR_DATA        (IB.WR_DATA),

    // Read interface (FrameLinks)
     .TX_DATA        (fl_data),
     .TX_SOF_N       (fl_sof_n),
     .TX_SOP_N       (fl_sop_n),
     .TX_EOP_N       (fl_eop_n),
     .TX_EOF_N       (fl_eof_n),
     .TX_REM         (fl_rem),
     .TX_SRC_RDY_N   (fl_src_rdy_n),
     .TX_DST_RDY_N   (fl_dst_rdy_n)
);

endmodule : DUT
