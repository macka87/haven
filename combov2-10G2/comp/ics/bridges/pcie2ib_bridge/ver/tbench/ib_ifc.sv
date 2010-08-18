//
// ib_ifc.pkg: System Verilog Internal Bus interface
// Copyright (C) 2007 CESNET
// Author(s): Tomas Malek <tomalek@liberouter.org>
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in
//    the documentation and/or other materials provided with the
//    distribution.
// 3. Neither the name of the Company nor the names of its contributors
//    may be used to endorse or promote products derived from this
//    software without specific prior written permission.
//
// This software is provided ``as is'', and any express or implied
// warranties, including, but not limited to, the implied warranties of
// merchantability and fitness for a particular purpose are disclaimed.
// In no event shall the company or contributors be liable for any
// direct, indirect, incidental, special, exemplary, or consequential
// damages (including, but not limited to, procurement of substitute
// goods or services; loss of use, data, or profits; or business
// interruption) however caused and on any theory of liability, whether
// in contract, strict liability, or tort (including negligence or
// otherwise) arising in any way out of the use of this software, even
// if advised of the possibility of such damage.
//
// $Id: ib_ifc.sv 688 2007-10-19 16:11:56Z tomalek $
//

// ----------------------------------------------------------------------------
//                        Interface declaration
// ----------------------------------------------------------------------------

// -- Internal Bus Interface --------------------------------------------------
interface iInternalBusLink (input logic CLK, RESET);
  
  logic [63:0] DATA;  // Data
  logic SOP_N;        // Start of Packet active in low
  logic EOP_N;        // End of Packet active in low
  logic SRC_RDY_N;    // Source data ready active in low
  logic DST_RDY_N;    // Destination data ready active in low

  // Receive Modport
  modport rx (input  CLK,
              input  RESET,
              input  DATA,
              input  SOP_N,
              input  EOP_N,
              input  SRC_RDY_N,
              output DST_RDY_N);
  
  // Transive Modport
  modport tx (input  CLK,
              input  RESET,
              output DATA,
              output SOP_N,
              output EOP_N,
              output SRC_RDY_N,
              input  DST_RDY_N);

  // Passive Modport
  modport monitor (input CLK,
                   input RESET,
                   input DATA,
                   input SOP_N,
                   input EOP_N,
                   input SRC_RDY_N,
                   input DST_RDY_N);



  // --------------------------------------------------------------------------
  // -- Interface properties/assertions
  // --------------------------------------------------------------------------

  // -- SOP together with EOP -------------------------------------------------
  // No SOP may be active together with EOP, because no Internal Bus
  // transaction is only one word long.
  property NoSOPEOP;
     @(posedge CLK) disable iff (RESET) SOP_N || EOP_N;
  endproperty

  assert property (NoSOPEOP)
     else $error("SOP_N and EOP_N signals are active at the same cycle.");
  
  
  // -- No data after EOP ----------------------------------------------------
  // After EOP, no data cannot be sent, until SOP is sent. EOP marks end of
  // transaction. First, we define a sequence of waiting for the first active
  // SOP. Then we declare, that after active cycle of EOP, there may be no
  // transfer during that sequence ( = until active SOP).
  sequence sop_seq;
     ##[0:$] (!SOP_N) && !(SRC_RDY_N || DST_RDY_N);
  endsequence

  property NoDataAfterEOP;
     @(posedge CLK) disable iff (RESET) 
        (!EOP_N) && !(SRC_RDY_N || DST_RDY_N) |=> 
	   !(SOP_N && !(SRC_RDY_N || DST_RDY_N)) throughout sop_seq;
  endproperty

  assert property (NoDataAfterEOP)
     else $error("InternalBus transaction continued after EOP_N.");

  // -- Matching EOP after SOP ------------------------------------------------
  // Each SOP must be, after some time, followed by EOP. Each transaction must
  // have its end. First, we define a sequence of waiting for the first active
  // EOP. Then we declare, that after active cycle of SOP, there may be no
  // another active SOP during that sequence ( = until active EOP).
  sequence eop_seq;
     ##[0:$] (!EOP_N) && !(SRC_RDY_N || DST_RDY_N);
  endsequence

  property EOPMatchSOP;
     @(posedge CLK) disable iff (RESET) 
        (!SOP_N) && !(SRC_RDY_N || DST_RDY_N) |=>
           (!((!SOP_N) && !(SRC_RDY_N || DST_RDY_N))) throughout eop_seq;
  endproperty

  assert property (EOPMatchSOP)
     else $error("SOP_N was not followed by matching EOP_N after some time");


endinterface 


// -- Internal Bus Master Interface -------------------------------------------
interface iIbBm64 (input logic CLK, RESET);

   logic [63:0] GLOBAL_ADDR;
   logic [31:0] LOCAL_ADDR;
   logic [11:0] LENGTH;
   logic [15:0] TAG;
   logic [ 1:0] TRANS_TYPE;
   logic        REQ;
   logic        ACK;
   logic [15:0] OP_TAG;
   logic        OP_DONE;

   modport driver (
      input  CLK, RESET, ACK, OP_TAG, OP_DONE,
      output GLOBAL_ADDR, LOCAL_ADDR, LENGTH, TAG, TRANS_TYPE, REQ
   );

   modport comp (
      input  CLK, RESET, GLOBAL_ADDR, LOCAL_ADDR, LENGTH, TAG, TRANS_TYPE, REQ,
      output ACK, OP_TAG, OP_DONE
   );

   modport monitor (
      input  CLK, RESET, ACK, OP_TAG, OP_DONE,
             GLOBAL_ADDR, LOCAL_ADDR, LENGTH, TAG, TRANS_TYPE, REQ
   );

endinterface

// -- Internal Bus Write Interface --------------------------------------------
interface iIbMiWrite64 (input logic CLK, RESET);
  logic [31:0] ADDR;
  logic [63:0] DATA;
  logic [7 :0] BE;
  logic        REQ;
  logic        RDY;
  logic [11:0] LENGTH;
  logic        SOF;
  logic        EOF;
 
  modport user (
     input  CLK, RESET, DATA, ADDR, BE, REQ, LENGTH, SOF, EOF,
     output RDY
     );

  modport endpoint (
     input  CLK, RESET, RDY,
     output DATA, ADDR, BE, REQ, LENGTH, SOF, EOF
  );

  modport monitor (
     input  CLK, RESET, DATA, ADDR, BE, REQ, LENGTH, SOF, EOF, RDY
  );
  
endinterface

// -- Internal Bus Read Interface ---------------------------------------------
interface iIbMiRead64 (input logic CLK, RESET);
  logic [31:0] ADDR;
  logic [7 :0] BE;
  logic        REQ;
  logic        ARDY;
  logic        SOF_IN;
  logic        EOF_IN;
  logic [63:0] DATA;
  logic        SRC_RDY;
  logic        DST_RDY;

  modport user (
    input  CLK, RESET, ADDR, BE, REQ, SOF_IN, EOF_IN, DST_RDY,
    output ARDY, DATA, SRC_RDY
  );

  modport endpoint (
      input  CLK, RESET, ARDY, DATA, SRC_RDY,
      output ADDR, BE, REQ, SOF_IN, EOF_IN, DST_RDY
  );

  modport monitor (
     input CLK, RESET, ADDR, BE, REQ, SOF_IN, EOF_IN, DST_RDY, ARDY, DATA, SRC_RDY
     );

endinterface



