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
 * $Id: dut.sv 7788 2009-03-26 21:02:28Z xsanta06 $
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
   iNFifoRx.nfifo_write FW[FLOWS],
   iNFifoRx.fifo_read   FR
);


// Signals for DUT conection
wire [DATA_WIDTH-1:0] fw_data_in;  
wire [FLOWS-1:0] fw_write;
wire [FLOWS-1:0] fw_full;
genvar i;

// Connecting FR to interfaces
generate
for (i=0; i<FLOWS; i++) begin
  assign fw_data_in[(i+1)*(DATA_WIDTH/FLOWS)-1:(DATA_WIDTH/FLOWS)*i] = FW[i].DATA_IN;
  assign fw_write[i]                                                 = FW[i].WRITE;
  assign FW[i].FULL                                                  = fw_full[i];
  end
endgenerate

// -------------------- Module body -------------------------------------------
NFIFO2FIFO #(
        .DATA_WIDTH     (DATA_WIDTH),
        .FLOWS          (FLOWS),
        .BLOCK_SIZE     (BLOCK_SIZE),
        .LUT_MEMORY     (LUT_MEMORY),
        .OUTPUT_REG     (OUTPUT_REG),
        .GLOB_STATE     (GLOB_STATE)
   )

   VHDL_DUT_U (
    // Common Interface
    
    //vyber signalov
    .CLK               (CLK),
    .RESET             (RESET),
 
    // Write interface
    .DATA_IN            (fw_data_in),
    .WRITE              (fw_write),
    .FULL               (fw_full),
    
    // Read interface
    .DATA_OUT           (FR.DATA_OUT),
    .DATA_VLD           (FR.DATA_VLD),
    .BLOCK_ADDR         (FR.BLOCK_ADDR),
    .READ               (FR.READ),
    .PIPE_EN            (FR.PIPE_EN),
    .EMPTY              (FR.EMPTY),
    
    .STATUS             (FR.STATUS)    
    );

endmodule : DUT
