/*
 * DUT.sv: Design under test
 * Copyright (C) 2009 CESNET
 * Author(s): Marcela Šimková <xsimko03@stud.fit.vutbr.cz>
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
 * $Id: dut.sv 9151 2009-07-06 08:41:24Z xsimko03 $
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
   input logic                  CLK,
   input logic                  RESET,
   iPacDmaCtrl.misc             PACDMA,
   iDmaCtrl.dma                 DMA,
   iPacDmaCtrl.statusrx         STAT,
   iPacDmaCtrl.descriptor       DESC,      
   iInternalBus.ib_read         IB,
   iFrameLinkRx.dut             FL[FLOWS]
);

// Signals for DUT conection

// FrameLink Interface
wire [BUFFER_DATA_WIDTH-1:0]  fl_data;  
wire [FLOWS-1:0]  fl_sop_n;
wire [FLOWS-1:0]  fl_eop_n;
wire [FLOWS-1:0]  fl_sof_n;
wire [FLOWS-1:0]  fl_eof_n;
wire [RXDREMWIDTH*FLOWS-1:0]  fl_rem;
wire [FLOWS-1:0]  fl_src_rdy_n;
wire [FLOWS-1:0]  fl_dst_rdy_n;

// Connecting FR to interfaces
generate
for (genvar i=0; i<FLOWS; i++) begin
  assign fl_data[(i+1)*RXDWIDTH-1:RXDWIDTH*i] = FL[i].DATA;
  assign fl_sop_n[i] = FL[i].SOP_N ;
  assign fl_eop_n[i] = FL[i].EOP_N ;
  assign fl_sof_n[i] = FL[i].SOF_N ;
  assign fl_eof_n[i] = FL[i].EOF_N ;
  assign fl_rem[(i+1)*RXDREMWIDTH-1:RXDREMWIDTH*i] = FL[i].DREM;
  assign fl_src_rdy_n[i] = FL[i].SRC_RDY_N;
  assign FL[i].DST_RDY_N = fl_dst_rdy_n[i] ;
end
endgenerate

// -------------------- Module body -------------------------------------------
rx_ctrl_buf_pac #(
        .FLOWS                  (FLOWS),
        .BUFFER_DATA_WIDTH      (BUFFER_DATA_WIDTH),
        .BUFFER_BLOCK_SIZE      (BUFFER_BLOCK_SIZE),
        .BUFFER_TOTAL_FLOW_SIZE (BUFFER_TOTAL_FLOW_SIZE),
        .CTRL_BUFFER_ADDR       (CTRL_BUFFER_ADDR),
        .CTRL_BUFFER_GAP        (CTRL_BUFFER_GAP),
        .CTRL_BUFFER_SIZE       (CTRL_BUFFER_SIZE),
        .CTRL_DMA_ID            (CTRL_DMA_ID),
        .CTRL_DMA_DATA_WIDTH    (CTRL_DMA_DATA_WIDTH),
        .CTRL_BLOCK_SIZE        (CTRL_BLOCK_SIZE)
   )

   VHDL_DUT_U  (
     // Common Interface
     .CLK            (CLK),
     .RESET          (RESET),
    
     // Misc signals 
     .RUN            (PACDMA.RUN),
     .IDLE           (PACDMA.IDLE),
 
     // Descriptor FIFO interface
     .DESC_READ      (DESC.DESC_READ),
     .DESC_ADDR      (DESC.DESC_ADDR), 
     .DESC_DO        (DESC.DESC_DO),
     .DESC_DO_VLD    (DESC.DESC_DO_VLD),
     .DESC_EMPTY     (DESC.DESC_EMPTY),
     
     // Status FIFO interface
     .SU_ADDR        (STAT.SU_ADDR),
     .SU_DATA        (STAT.SU_DATA_RX), 
     .SU_DATA_VLD    (STAT.SU_DATA_VLD),
     .SU_HFULL       (STAT.SU_HFULL),
          
     // DMA Interface 
     .DMA_ADDR       (DMA.DMA_ADDR),
     .DMA_DOUT       (DMA.DMA_DOUT),
     .DMA_REQ        (DMA.DMA_REQ),
     .DMA_ACK        (DMA.DMA_ACK),
     .DMA_DONE       (DMA.DMA_DONE),
     .DMA_TAG        (DMA.DMA_TAG),
     
     // Read signals (InternalBus) 
     .RD_ADDR        (IB.RD_ADDR),
     .RD_BE          (IB.RD_BE),
     .RD_REQ         (IB.RD_REQ),
     .RD_ARDY        (IB.RD_ARDY),
     .RD_DATA        (IB.RD_DATA),
     .RD_SRC_RDY     (IB.RD_SRC_RDY),
     .RD_DST_RDY     (IB.RD_DST_RDY),
     
     // Write interface (FrameLinks)
     .RX_DATA        (fl_data),
     .RX_SOF_N       (fl_sof_n),
     .RX_SOP_N       (fl_sop_n),
     .RX_EOP_N       (fl_eop_n),
     .RX_EOF_N       (fl_eof_n),
     .RX_REM         (fl_rem),
     .RX_SRC_RDY_N   (fl_src_rdy_n),
     .RX_DST_RDY_N   (fl_dst_rdy_n)
);

endmodule : DUT
