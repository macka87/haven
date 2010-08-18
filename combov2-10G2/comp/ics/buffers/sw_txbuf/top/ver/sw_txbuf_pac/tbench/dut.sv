/*
 * DUT.sv: Design under test
 * Copyright (C) 2008 CESNET
 * Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
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
 * $Id: dut.sv 7853 2009-03-28 20:31:01Z xsimko03 $
 *
 * TODO:
 *
 */
 
// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants
import math_pkg::*;       // log2()

module DUT (
   input logic CLK,
   input logic RESET,
   txBuffWrite.writeBuff BW,                    // Write Interface
   txBuffRead.readBuff   BR[FLOWS],             // Read Interface
   txBuffRead.readBuff   MONITOR[FLOWS]         // Monitor Interface
);

/// Signals for DUT conection
wire [FLOWS-1:0] br_tx_dst_rdy_n;
wire [TX_DATA_WIDTH*FLOWS-1:0] br_tx_data; 
wire [FLOWS-1:0] br_tx_sof_n;
wire [FLOWS-1:0] br_tx_sop_n;
wire [FLOWS-1:0] br_tx_eop_n;
wire [FLOWS-1:0] br_tx_eof_n;
wire [(log2((TX_DATA_WIDTH)/8)*FLOWS)-1:0] br_tx_rem;
wire [FLOWS-1:0] br_tx_src_rdy_n;
genvar i;

// Connecting BR to interfaces
generate
for (i=0; i<FLOWS; i++) begin
  assign br_tx_dst_rdy_n[i]  = BR[i].TX_DST_RDY_N;
  assign BR[i].TX_DATA       = br_tx_data[(i+1)*(TX_DATA_WIDTH)-1:(TX_DATA_WIDTH)*i];
  assign BR[i].TX_SOF_N      = br_tx_sof_n[i];
  assign BR[i].TX_SOP_N      = br_tx_sop_n[i];
  assign BR[i].TX_EOP_N      = br_tx_eop_n[i];
  assign BR[i].TX_EOF_N      = br_tx_eof_n[i];
  assign BR[i].TX_REM        = br_tx_rem[(i+1)*(log2(TX_DATA_WIDTH/8))-1:(log2(TX_DATA_WIDTH/8))*i];
  assign BR[i].TX_SRC_RDY_N  = br_tx_src_rdy_n[i];
  
  
  end
endgenerate

// -------------------- Module body -------------------------------------------
//TODO: ZMENA NAZVU TESTOVANEJ KOMPONENTY, 
//V PRIPADE PRIDANIA ROZHRANI TREBA PRIDAT AJ PORTY
SW_TXBUF_PAC_TOP #(
        .DATA_WIDTH      (DATA_WIDTH),
        .FLOWS           (FLOWS),
        .BLOCK_SIZE      (BLOCK_SIZE),
        .TOTAL_FLOW_SIZE (TOTAL_FLOW_SIZE)
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK               (CLK),
     .RESET             (RESET),
 
    // Write interface
    .WR_ADDR            (BW.WR_ADDR),
    .WR_BE              (BW.WR_BE),
    .WR_REQ             (BW.WR_REQ),
    .WR_DATA            (BW.WR_DATA),
    .WR_RDY             (BW.WR_RDY),
    .TX_NEWLEN          (BW.TX_NEWLEN),
    .TX_NEWLEN_DV       (BW.TX_NEWLEN_DV),
    .TX_NEWLEN_RDY      (BW.TX_NEWLEN_RDY),
    .TX_RELLEN          (BW.TX_RELLEN),
    .TX_RELLEN_DV       (BW.TX_RELLEN_DV),
    
    // Read interface
    .TX_DST_RDY_N       (br_tx_dst_rdy_n),
    .TX_DATA            (br_tx_data),
    .TX_SOF_N           (br_tx_sof_n),
    .TX_SOP_N           (br_tx_sop_n),
    .TX_EOP_N           (br_tx_eop_n),
    .TX_EOF_N           (br_tx_eof_n),
    .TX_REM             (br_tx_rem),
    .TX_SRC_RDY_N       (br_tx_src_rdy_n) 
    );


endmodule : DUT
