/*
 * DUT.sv: Design under test
 * Copyright (C) 2010 CESNET
 * Author(s): Marek Santa <santa@liberouter.org>
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
 * $Id: dut.sv 14346 2010-07-13 13:38:11Z xsanta06 $
 *
 * TODO:
 *
 */
 
// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module DUT (
   input logic               RESET,
   input logic               CLK,
   iTagSequencerUsr.dut      USR,
   iTagSequencerEp.dut       EP
);


// -------------------- Module body -------------------------------------------
TAG_SEQUENCER#(
      .EP_TAG_WIDTH     (EP_TAG_WIDTH),
      .USR_TAG_WIDTH    (USR_TAG_WIDTH)
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK            (CLK),
     .RESET          (RESET),
    
    // UP direction 
     .USR_TAG            (USR.TAG),
     .USR_REQ            (USR.REQ),
     .USR_ACK            (USR.ACK),
     .USR_TRANS_TYPE     (USR.TRANS_TYPE),
     .EP_TAG             (EP.TAG),
     .EP_REQ             (EP.REQ),
     .EP_ACK             (EP.ACK),
     .EP_TRANS_TYPE      (EP.TRANS_TYPE),

    // DOWN direction
     .EP_OP_TAG          (EP.OP_TAG),
     .EP_OP_DONE         (EP.OP_DONE),
     .USR_OP_TAG         (USR.OP_TAG),
     .USR_OP_DONE        (USR.OP_DONE),

    // Stats 
     .FULL               (FULL),
     .EMPTY              (EMPTY)
);


endmodule : DUT
