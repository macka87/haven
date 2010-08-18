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
 * $Id: dut.sv 2749 2008-06-17 22:23:51Z xsanta06 $
 *
 * TODO:
 *
 */
 
// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
// obsahuje pouzite parametre
import test_pkg::*; // Test constants
import math_pkg::*;       // log2()

module DUT (
   input logic CLK,
   input logic RESET,
   iNFifoTx.fifo_write FW,
   iNFifoTx.nfifo_read  FR[FLOWS],
   iNFifoTx.nfifo_read  MONITOR[FLOWS]
);


// Signals for DUT conection
wire [DATA_WIDTH-1:0] fr_data_out;  
wire [FLOWS-1:0] fr_data_vld;
wire [FLOWS-1:0] fr_read;
wire [FLOWS-1:0] fr_empty;
wire [log2(BLOCK_SIZE+1)*FLOWS-1:0] fr_status;
genvar i;

// Connecting FR to interfaces
generate
for (i=0; i<FLOWS; i++) begin
  assign FR[i].DATA_OUT  = fr_data_out[(i+1)*(DATA_WIDTH/FLOWS)-1:(DATA_WIDTH/FLOWS)*i];
  assign FR[i].DATA_VLD  = fr_data_vld[i];
  assign fr_read[i]      = FR[i].READ;
  assign FR[i].EMPTY     = fr_empty[i];
  assign FR[i].STATUS    = fr_status[(i+1)*log2(BLOCK_SIZE+1)-1:log2(BLOCK_SIZE+1)*i];
  end
endgenerate

// -------------------- Module body -------------------------------------------
FIFO2NFIFO #(
        .DATA_WIDTH     (DATA_WIDTH),
        .FLOWS          (FLOWS),
        .BLOCK_SIZE     (BLOCK_SIZE),
        .LUT_MEMORY     (LUT_MEMORY),
        .GLOB_STATE     (GLOB_STATE)
   )

   VHDL_DUT_U (
    // Common Interface
    
    //vyber signalov
    .CLK               (CLK),
    .RESET             (RESET),
 
    // Write interface
    .DATA_IN            (FW.DATA_IN),
    .BLOCK_ADDR         (FW.BLOCK_ADDR),
    .WRITE              (FW.WRITE),
    .FULL               (FW.FULL),
    
    // Read interface
    .DATA_OUT           (fr_data_out),
    .DATA_VLD           (fr_data_vld),
    .READ               (fr_read),
    .EMPTY              (fr_empty),
    
    .STATUS             (fr_status)    
    );

endmodule : DUT
