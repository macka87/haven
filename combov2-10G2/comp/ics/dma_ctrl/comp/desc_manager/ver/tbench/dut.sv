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
 * $Id: dut.sv 4366 2008-08-05 12:44:17Z xsanta06 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------

import test_pkg::*;        // Test constants

// Design Under Test
module DUT (
   input logic CLK,
   input logic RESET,
   descManagerWrite.writeDesc           DW,             // Write Interface
   descManagerRead.readDesc             DR[FLOWS],      // Read Interface
   descManagerRead.readDesc             MONITOR[FLOWS]  // Monitor Interface
);


// Signals for DUT conection
wire [63:0]      dr_data_out;
wire [FLOWS-1:0] dr_empty;
wire [FLOWS-1:0] dr_read;
genvar i;

// Connecting DR to interfaces
generate
for (i=0; i<FLOWS; i++) begin
  assign dr_read[i]          = DR[i].READ;
  assign DR[i].DATA_OUT      = dr_data_out[(i+1)*(64/FLOWS)-1:(64/FLOWS)*i];
  assign DR[i].EMPTY         = dr_empty[i];
  end
endgenerate

// -------------------- Module body -------------------------------------------
desc_manager_wrapper #(
        .VLOG_BASE_ADDR      (BASE_ADDR),
        .FLOWS          (FLOWS),
        .BLOCK_SIZE     (BLOCK_SIZE)
        )

   VHDL_DUT_U (
    // Common Interface
    
    .CLK                (CLK),
    .RESET              (RESET),
 
    // Write interface
    .WR_ADDR            (DW.WR_ADDR),
    .WR_BE              (DW.WR_BE),
    .WR_REQ             (DW.WR_REQ),
    .WR_DATA            (DW.WR_DATA),
    .WR_RDY             (DW.WR_RDY),
    .BM_GLOBAL_ADDR     (DW.BM_GLOBAL_ADDR),
    .BM_LOCAL_ADDR      (DW.BM_LOCAL_ADDR),
    .BM_LENGTH          (DW.BM_LENGTH),
    .BM_REQ             (DW.BM_REQ),
    .BM_ACK             (DW.BM_ACK),
    .ENABLE             (DW.ENABLE),
    
    // Read interface
    .DATA_OUT           (dr_data_out),
    .EMPTY              (dr_empty),
    .READ               (dr_read)
    );

endmodule : DUT
