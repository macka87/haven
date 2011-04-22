/*
 * DUT.sv: Design under test
 * Copyright (C) 2009 CESNET
 * Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
 * $Id: dut.sv 10612 2009-08-21 14:10:15Z xkosar02 $
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
   iFrameLinkTx.dut TX,
   iFrameLinkTx.dut MONITOR,
   iMi32.dut        MI32_RXTX
);

// -------------------- Module body -------------------------------------------
HGEN #(
     .DATA_WIDTH     (RX_DATA_WIDTH),
     .UH_SIZE        (UH_SIZE),
     .FLOWID_WIDTH   (FLOWID_WIDTH),
     .ITEMS          (ITEMS)
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK           (CLK),
     .RESET         (RESET),
 
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
     
     .MI_DWR        (MI32_RXTX.DWR),
     .MI_ADDR       (MI32_RXTX.ADDR),
     .MI_RD         (MI32_RXTX.RD),
     .MI_WR         (MI32_RXTX.WR),
     .MI_BE         (MI32_RXTX.BE),
     .MI_DRD        (MI32_RXTX.DRD),
     .MI_ARDY       (MI32_RXTX.ARDY),
     .MI_DRDY       (MI32_RXTX.DRDY),
     
     .MASK          (HGEN_MASK)
);


endmodule : DUT
