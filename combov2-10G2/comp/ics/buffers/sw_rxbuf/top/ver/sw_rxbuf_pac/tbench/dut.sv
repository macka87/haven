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
 * $Id: dut.sv 7929 2009-04-01 09:53:34Z xsanta06 $
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
   iSwRxBuffer.fl FL[FLOWS],
   iSwRxBuffer.ib IB
);

// Signals for DUT conection
wire [DATA_WIDTH-1:0] rx_data;  
wire [FLOWS-1:0] rx_sop_n;
wire [FLOWS-1:0] rx_eop_n;
wire [FLOWS-1:0] rx_sof_n;
wire [FLOWS-1:0] rx_eof_n;
wire [REM_WIDTH*FLOWS-1:0] rx_rem;
wire [FLOWS-1:0] rx_src_rdy_n;
wire [FLOWS-1:0] rx_dst_rdy_n;
genvar i;

// Connecting FR to interfaces
generate
for (i=0; i<FLOWS; i++) begin
// input                  ---   output
  assign rx_data[(i+1)*RX_DATA_WIDTH-1:RX_DATA_WIDTH*i] = FL[i].RX_DATA;
  assign rx_sop_n[i]                   = FL[i].RX_SOP_N;
  assign rx_eop_n[i]                   = FL[i].RX_EOP_N;
  assign rx_sof_n[i]                   = FL[i].RX_SOF_N;
  assign rx_eof_n[i]                   = FL[i].RX_EOF_N;
  assign rx_rem[(i+1)*REM_WIDTH-1:REM_WIDTH*i]  = FL[i].RX_REM;
  assign rx_src_rdy_n[i]               = FL[i].RX_SRC_RDY_N;
  assign FL[i].RX_DST_RDY_N            = rx_dst_rdy_n[i];
  end
endgenerate

// -------------------- Module body -------------------------------------------
//TODO: ZMENA NAZVU TESTOVANEJ KOMPONENTY, 
//V PRIPADE PRIDANIA ROZHRANI TREBA PRIDAT AJ PORTY
SW_RXBUF_PAC_TOP #(
        .DATA_WIDTH      (DATA_WIDTH),
        .FLOWS           (FLOWS),
        .BLOCK_SIZE      (BLOCK_SIZE),
        .TOTAL_FLOW_SIZE (TOTAL_FLOW_SIZE)
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK               (CLK),
     .RESET             (RESET),
 
    // Receive port
     .RX_DATA       (rx_data),
     .RX_REM        (rx_rem),
     .RX_SOF_N      (rx_sof_n),
     .RX_EOF_N      (rx_eof_n),
     .RX_SOP_N      (rx_sop_n),
     .RX_EOP_N      (rx_eop_n),
     .RX_SRC_RDY_N  (rx_src_rdy_n),
     .RX_DST_RDY_N  (rx_dst_rdy_n),
     .RX_NEWLEN     (IB.RX_NEWLEN),
     .RX_NEWLEN_DV  (IB.RX_NEWLEN_DV),
     .RX_NEWLEN_RDY (IB.RX_NEWLEN_RDY),
     .RX_RELLEN     (IB.RX_RELLEN),
     .RX_RELLEN_DV  (IB.RX_RELLEN_DV),

    // Transitive port
     .RD_DATA       (IB.RD_DATA),
     .RD_ADDR       (IB.RD_ADDR),
     .RD_BE         (IB.RD_BE),
     .RD_REQ        (IB.RD_REQ),
     .RD_ARDY       (IB.RD_ARDY),
     .RD_SRC_RDY    (IB.RD_SRC_RDY),
     .RD_DST_RDY    (IB.RD_DST_RDY)
);


endmodule : DUT
