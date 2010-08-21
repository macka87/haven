/*
 * DUT.sv: Design under test
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobiersky <kobiersky@liberouter.org>
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
 * $Id: dut.sv 14975 2010-08-11 09:27:06Z xjanal01 $
 *
 * TODO:
 *
 */
 
// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

//V PRIPADE POTREBY SA MOZE DOPLNIT VIAC FRAMELINKOVYCH ROZHRANI DANEHO TYPU
module DUT (
   input logic CLK,
   input logic RESET,
   iFrameLinkRx.dut RX,
   iFrameLinkTx.dut TX,
   iFrameLinkTx.dut MONITOR,
   iMi32.dut        MI32_RXTX
);

// -------------------- Module body -------------------------------------------
//TODO: ZMENA NAZVU TESTOVANEJ KOMPONENTY, 
//V PRIPADE PRIDANIA ROZHRANI TREBA PRIDAT AJ PORTY
FL_MASKER #(
     //.RX_DATA_WIDTH(RX_DATA_WIDTH),
     //.TX_DATA_WIDTH(TX_DATA_WIDTH)
     .FL_WIDTH(FL_WIDTH),
     .NUMBER_OF_WORDS(NUMBER_OF_WORDS),
     .RX_PIPE(RX_PIPE),
     .TX_PIPE(TX_PIPE)
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK               (CLK),
     .RESET             (RESET),
 
    // Port 0
     .RX_DATA       (RX.DATA),
     .RX_REM        (RX.DREM),
     .RX_SOF_N      (RX.SOF_N),
     .RX_EOF_N      (RX.EOF_N),
     .RX_SOP_N      (RX.SOP_N),
     .RX_EOP_N      (RX.EOP_N),
     .RX_SRC_RDY_N  (RX.SRC_RDY_N),
     .RX_DST_RDY_N  (RX.DST_RDY_N),

    // Port 0
     .TX_DATA       (TX.DATA),
     .TX_REM        (TX.DREM),
     .TX_SOF_N      (TX.SOF_N),
     .TX_EOF_N      (TX.EOF_N),
     .TX_SOP_N      (TX.SOP_N),
     .TX_EOP_N      (TX.EOP_N),
     .TX_SRC_RDY_N  (TX.SRC_RDY_N),
     .TX_DST_RDY_N  (TX.DST_RDY_N),

     .RESET_VALUE   (RESET_VALUE),

     .MI32_DWR        (MI32_RXTX.DWR),
     .MI32_ADDR       (MI32_RXTX.ADDR),
     .MI32_RD         (MI32_RXTX.RD),
     .MI32_WR         (MI32_RXTX.WR),
     .MI32_BE         (MI32_RXTX.BE),
     .MI32_DRD        (MI32_RXTX.DRD),
     .MI32_ARDY       (MI32_RXTX.ARDY),
     .MI32_DRDY       (MI32_RXTX.DRDY)
);


endmodule : DUT
