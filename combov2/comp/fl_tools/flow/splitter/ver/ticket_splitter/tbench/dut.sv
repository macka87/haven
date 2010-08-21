/*
 * DUT.sv: Design under test
 * Copyright (C) 2009 CESNET
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
 * $Id: dut.sv 10588 2009-08-21 09:02:15Z xsanta06 $
 *
 * TODO:
 *
 */
 
// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module DUT (
   input logic CLK,
   input logic RESET,
   iFrameLinkRx.dut RX,
   iFrameLinkTx.dut TX[OUTPUT_COUNT],
   iControl.dut_in  CTRL_IN,
   iControl.dut_out CTRL_OUT[OUTPUT_COUNT]
);

// Signals for DUT conection
wire [(OUTPUT_COUNT*TX_DATA_WIDTH)-1:0] tx_data;  
wire [(OUTPUT_COUNT*TX_DREM_WIDTH)-1:0] tx_drem;
wire [OUTPUT_COUNT-1:0] tx_sof_n;
wire [OUTPUT_COUNT-1:0] tx_eof_n;
wire [OUTPUT_COUNT-1:0] tx_sop_n;
wire [OUTPUT_COUNT-1:0] tx_eop_n;
wire [OUTPUT_COUNT-1:0] tx_src_rdy_n;
wire [OUTPUT_COUNT-1:0] tx_dst_rdy_n;
wire [(OUTPUT_COUNT*TICKET_WIDTH)-1:0] ctrl_data_out;  
wire [OUTPUT_COUNT-1:0] ctrl_data_out_vld;
wire [OUTPUT_COUNT-1:0] ctrl_data_out_rq;

// Connecting TX to interfaces
generate
for (genvar i=0; i<OUTPUT_COUNT; i++) begin
  assign TX[i].DATA  = tx_data[(i+1)*TX_DATA_WIDTH-1:TX_DATA_WIDTH*i];
  assign TX[i].DREM  = tx_drem[(i+1)*TX_DREM_WIDTH-1:TX_DREM_WIDTH*i];
  assign TX[i].SOF_N = tx_sof_n[i];
  assign TX[i].EOF_N = tx_eof_n[i];
  assign TX[i].SOP_N = tx_sop_n[i];
  assign TX[i].EOP_N = tx_eop_n[i];
  assign TX[i].SRC_RDY_N = tx_src_rdy_n[i];
  assign tx_dst_rdy_n[i] = TX[i].DST_RDY_N;

  assign CTRL_OUT[i].CTRL_DATA_OUT  = ctrl_data_out[(i+1)*TICKET_WIDTH-1:TICKET_WIDTH*i];
  assign CTRL_OUT[i].CTRL_DATA_OUT_VLD = ctrl_data_out_vld[i];
  assign ctrl_data_out_rq[i] = CTRL_OUT[i].CTRL_DATA_OUT_RQ;
  end
endgenerate



// -------------------- Module body -------------------------------------------
FL_TICKET_SPLITTER_FIFO2NFIFO#(
     .RX_DATA_WIDTH     (RX_DATA_WIDTH),
     .TX_DATA_WIDTH     (TX_DATA_WIDTH),
     .OUTPUT_COUNT      (OUTPUT_COUNT),
     .FRAME_PARTS       (FRAME_PARTS),
     .TICKET_WIDTH      (TICKET_WIDTH),
     .TICKET_FIFO_ITEMS (TICKET_FIFO_ITEMS)    
      )

   VHDL_DUT_U  (
    // Common Interface
     .CLK               (CLK),
     .RESET             (RESET),
 
    // Receive port
     .RX_DATA       (RX.DATA),
     .RX_REM        (RX.DREM),
     .RX_SOF_N      (RX.SOF_N),
     .RX_EOF_N      (RX.EOF_N),
     .RX_SOP_N      (RX.SOP_N),
     .RX_EOP_N      (RX.EOP_N),
     .RX_SRC_RDY_N  (RX.SRC_RDY_N),
     .RX_DST_RDY_N  (RX.DST_RDY_N),

     // Input control port
     .CTRL_DATA_IN     (CTRL_IN.CTRL_DATA_IN),     
     .CTRL_DATA_IN_VLD (CTRL_IN.CTRL_DATA_IN_VLD),
     .CTRL_DATA_IN_RQ  (CTRL_IN.CTRL_DATA_IN_RQ),
     
     // Transitive ports
     .TX_DATA       (tx_data),
     .TX_REM        (tx_drem),
     .TX_SOF_N      (tx_sof_n),
     .TX_EOF_N      (tx_eof_n),
     .TX_SOP_N      (tx_sop_n),
     .TX_EOP_N      (tx_eop_n),
     .TX_SRC_RDY_N  (tx_src_rdy_n),
     .TX_DST_RDY_N  (tx_dst_rdy_n),

     // Output control port
     .CTRL_DATA_OUT     (ctrl_data_out),
     .CTRL_DATA_OUT_VLD (ctrl_data_out_vld),
     .CTRL_DATA_OUT_RQ  (ctrl_data_out_rq)
);


endmodule : DUT
