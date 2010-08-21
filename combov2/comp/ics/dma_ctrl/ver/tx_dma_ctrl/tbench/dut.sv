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
 * $Id: dut.sv 12979 2010-02-26 16:13:08Z kastovsky $
 *
 * TODO:
 *
 */
 
// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants
import math_pkg::*; // log2

module DUT (
   input logic           CLK,
   input logic           RESET,
   iMi32.dut             SW,
   iInternalBus.ib_write IB,
   iDmaCtrl.misc         MISC[BUFFER_FLOWS],
   iDmaCtrl.descriptor   DESC[BUFFER_FLOWS],
   iDmaCtrl.dma          DMA[BUFFER_FLOWS],
   iFrameLinkTx.dut      FL[BUFFER_FLOWS],
   iFrameLinkTx.dut      MONITOR[BUFFER_FLOWS]
);

// Signals for DUT conection

// Misc signals Interface
wire [BUFFER_FLOWS-1:0]  interrupt;

// Descriptor Fifo Interface
wire [BUFFER_FLOWS-1:0]  desc_read;
wire [BUFFER_FLOWS*CTRL_DMA_DATA_WIDTH-1:0]  desc_do;
wire [BUFFER_FLOWS-1:0]  desc_empty;
wire [BUFFER_FLOWS-1:0]  desc_enable;

// DMA Interface
wire [BUFFER_FLOWS*log2(128/CTRL_DMA_DATA_WIDTH)-1:0]  dma_addr;
wire [BUFFER_FLOWS*CTRL_DMA_DATA_WIDTH-1:0]  dma_dout;
wire [BUFFER_FLOWS-1:0]  dma_req;
wire [BUFFER_FLOWS-1:0]  dma_ack;
wire [BUFFER_FLOWS-1:0]  dma_done;
wire [BUFFER_FLOWS*16-1:0]  dma_tag;

// FrameLink Interface
wire [BUFFER_DATA_WIDTH-1:0]  fl_data;  
wire [BUFFER_FLOWS-1:0]  fl_sop_n;
wire [BUFFER_FLOWS-1:0]  fl_eop_n;
wire [BUFFER_FLOWS-1:0]  fl_sof_n;
wire [BUFFER_FLOWS-1:0]  fl_eof_n;
wire [TXDREMWIDTH*BUFFER_FLOWS-1:0]  fl_rem;
wire [BUFFER_FLOWS-1:0]  fl_src_rdy_n;
wire [BUFFER_FLOWS-1:0]  fl_dst_rdy_n;

// Connecting FR to interfaces
generate
for (genvar i=0; i<BUFFER_FLOWS; i++) begin
  assign MISC[i].INTERRUPT   = interrupt[i];

  assign DESC[i].DESC_READ   = desc_read[i];
  assign DESC[i].DESC_ENABLE = desc_enable[i];
  assign desc_do[(i+1)*CTRL_DMA_DATA_WIDTH-1:CTRL_DMA_DATA_WIDTH*i] = DESC[i].DESC_DO;
  assign desc_empty[i]   = DESC[i].DESC_EMPTY;
    
  assign DMA[i].DMA_DOUT = dma_dout[(i+1)*CTRL_DMA_DATA_WIDTH-1:CTRL_DMA_DATA_WIDTH*i];
  assign DMA[i].DMA_REQ  = dma_req[i];
  assign dma_addr[(i+1)*log2(128/CTRL_DMA_DATA_WIDTH)-1:log2(128/CTRL_DMA_DATA_WIDTH)*i] = DMA[i].DMA_ADDR;
  assign dma_ack[i]      = DMA[i].DMA_ACK;
  assign dma_done[i]     = DMA[i].DMA_DONE;
  assign dma_tag[(i+1)*16-1:16*i] = DMA[i].DMA_TAG;
  
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
tx_dma_ctrl_opt_buf_wrapper #(
        .BUFFER_DATA_WIDTH      (BUFFER_DATA_WIDTH),
        .BUFFER_BLOCK_SIZE      (BUFFER_BLOCK_SIZE),
        .BUFFER_FLOWS           (BUFFER_FLOWS),
        .BUFFER_TOTAL_FLOW_SIZE (BUFFER_TOTAL_FLOW_SIZE),
        .BUFFER_SIZE_LENGTH     (BUFFER_SIZE_LENGTH),
        .BUFFER_USE_FL_PIPE     (BUFFER_USE_FL_PIPE),
        .CTRL_BUFFER_ADDR       (CTRL_BUFFER_ADDR),
        .CTRL_DMA_DATA_WIDTH    (CTRL_DMA_DATA_WIDTH)
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK            (CLK),
     .RESET          (RESET),
    
    // Misc signals 
     .INTERRUPT      (interrupt),
 
    // Descriptor FIFO interface
     .DESC_READ      (desc_read),
     .DESC_DO        (desc_do),
     .DESC_EMPTY     (desc_empty),
     .DESC_ENABLE    (desc_enable),
     
    // Memory interface 
     .SW_DWR         (SW.DWR),
     .SW_ADDR        (SW.ADDR),
     .SW_RD          (SW.RD),
     .SW_WR          (SW.WR),
     .SW_BE          (SW.BE),
     .SW_DRD         (SW.DRD),
     .SW_ARDY        (SW.ARDY),
     .SW_DRDY        (SW.DRDY),
     
    // DMA Interface 
     .DMA_ADDR       (dma_addr),
     .DMA_DOUT       (dma_dout),
     .DMA_REQ        (dma_req),
     .DMA_ACK        (dma_ack),
     .DMA_DONE       (dma_done),
     .DMA_TAG        (dma_tag),
     
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
