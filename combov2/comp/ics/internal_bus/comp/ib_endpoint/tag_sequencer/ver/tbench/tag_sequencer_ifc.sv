/*
 * tag_sequencer_ifc.sv: Tag Sequencer Interface
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
 * $Id: tag_sequencer_ifc.sv 14346 2010-07-13 13:38:11Z xsanta06 $
 *
 * TODO:
 *
 */
 

// ----------------------------------------------------------------------------
//                      Tag Sequencer Interface declaration
// ----------------------------------------------------------------------------

// -- Tag Sequencer Interface -------------------------------------------------
interface iTagSequencerUsr #(TAGWIDTH=8) (input logic CLK, RESET);  
  logic [TAGWIDTH-1:0] TAG    = 0;  // Tag
  logic REQ                   = 0;  // Request
  logic ACK                      ;  // Acknowledge
  logic [1:0] TRANS_TYPE      = 0;  // Transaction type
  logic [TAGWIDTH-1:0] OP_TAG    ;  // Tag
  logic OP_DONE                  ;  // Done
  

  clocking cb @(posedge CLK);
    input  ACK;
    output TAG, REQ, TRANS_TYPE;  
  endclocking: cb;

  clocking op_cb @(posedge CLK);
    input OP_TAG, OP_DONE;
  endclocking: op_cb;
  
  // DUT Modport
  modport dut (input  TAG,
               input  REQ,
               output ACK,
               input  TRANS_TYPE,
               output OP_TAG,
               output OP_DONE);
  
  // Testbench Modport
  modport tb    (clocking cb);
  modport op_tb (clocking op_cb);

endinterface : iTagSequencerUsr



// -- Tag Sequencer Interface -----------------------------------------------
interface iTagSequencerEp #(TAGWIDTH=8) (input logic CLK, RESET);  
  logic [TAGWIDTH-1:0] TAG       ;  // Tag
  logic REQ                      ;  // Request
  logic ACK                   = 0;  // Acknowledge
  logic [1:0] TRANS_TYPE         ;  // Transaction type
  logic [TAGWIDTH-1:0] OP_TAG = 0;  // Tag
  logic OP_DONE               = 0;  // Done
  

  clocking cb @(posedge CLK);
    input  TAG, REQ, TRANS_TYPE;  
    output ACK;
  endclocking: cb;

  clocking op_cb @(posedge CLK);
    output OP_TAG, OP_DONE;
  endclocking: op_cb;

  // DUT Modport
  modport dut (output TAG,
               output REQ,
               input  ACK,
               output TRANS_TYPE,
               input  OP_TAG,
               input  OP_DONE);
  
  // Testbench Modport
  modport tb    (clocking cb);
  modport op_tb (clocking op_cb);
  
endinterface : iTagSequencerEp
