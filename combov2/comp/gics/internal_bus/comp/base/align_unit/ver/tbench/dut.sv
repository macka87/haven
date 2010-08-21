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
 * $Id: dut.sv 3590 2008-07-16 09:05:59Z xsanta06 $
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
   iAlignUnit.rx RX,
   iAlignUnit.tx TX,
   iAlignUnit.tx MONITOR
);

// -------------------- Module body -------------------------------------------
//TODO: ZMENA NAZVU TESTOVANEJ KOMPONENTY, 
//V PRIPADE PRIDANIA ROZHRANI TREBA PRIDAT AJ PORTY
ALIGN_UNIT 

   VHDL_DUT_U  (
    // Common Interface
     .CLK               (CLK),
     .RESET             (RESET),
 
    // Receive port
     .IN_DATA       (RX.IN_DATA),
     .IN_SOF        (RX.IN_SOF),
     .IN_EOF        (RX.IN_EOF),
     .IN_SRC_RDY    (RX.IN_SRC_RDY),
     .IN_DST_RDY    (RX.IN_DST_RDY),
     .SRC_ADDR      (RX.SRC_ADDR),
     .DST_ADDR      (RX.DST_ADDR),
     .DATA_LEN      (RX.DATA_LEN),

    // Transitive port
     .OUT_DATA      (TX.OUT_DATA),
     .OUT_SOF       (TX.OUT_SOF),
     .OUT_EOF       (TX.OUT_EOF),
     .OUT_SRC_RDY   (TX.OUT_SRC_RDY),
     .OUT_DST_RDY   (TX.OUT_DST_RDY)     
);


endmodule : DUT
