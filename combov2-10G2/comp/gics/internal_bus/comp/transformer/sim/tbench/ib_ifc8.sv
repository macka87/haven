/*
 * ib_ifc8.pkg: System Verilog Internal Bus interface
 * Copyright (C) 2008 CESNET
 * Author(s): Tomas Malek <tomalek@liberouter.org>
 *            Petr Kobiersky <kobiersky@liberouter.org>
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
 * $Id: ib_ifc8.sv 1899 2008-03-26 15:52:13Z tomalek $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Interface declaration
// ----------------------------------------------------------------------------

// -- Internal Bus Interface --------------------------------------------------
interface iIB8 (input logic CLK, RESET);
  
  logic [7:0] DATA;   // Data
  logic SOF_N;        // Start of Packet active in low
  logic EOF_N;        // End of Packet active in low
  logic SRC_RDY_N;    // Source data ready active in low
  logic DST_RDY_N;    // Destination data ready active in low

  // Receive Modport
  modport rx (input  CLK,
              input  RESET,
              input  DATA,
              input  SOF_N,
              input  EOF_N,
              input  SRC_RDY_N,
              output DST_RDY_N);
  
  // Transive Modport
  modport tx (input  CLK,
              input  RESET,
              output DATA,
              output SOF_N,
              output EOF_N,
              output SRC_RDY_N,
              input  DST_RDY_N);

  // Passive Modport
  modport monitor (input CLK,
                   input RESET,
                   input DATA,
                   input SOF_N,
                   input EOF_N,
                   input SRC_RDY_N,
                   input DST_RDY_N);

  // --------------------------------------------------------------------------
  // -- Interface properties/assertions
  // --------------------------------------------------------------------------

  // -- SOF together with EOF -------------------------------------------------
  // No SOF may be active together with EOF, because no Internal Bus
  // transaction is only one word long.
  property NoSOFEOF;
     @(posedge CLK) disable iff (RESET) SOF_N || EOF_N;
  endproperty

  assert property (NoSOFEOF)
     else $error("SOF_N and EOF_N signals are active at the same cycle.");
  
  
  // -- No data after EOF ----------------------------------------------------
  // After EOF, no data cannot be sent, until SOF is sent. EOF marks end of
  // transaction. First, we define a sequence of waiting for the first active
  // SOF. Then we declare, that after active cycle of EOF, there may be no
  // transfer during that sequence ( = until active SOF).
  sequence sop_seq;
     ##[0:$] (!SOF_N) && !(SRC_RDY_N || DST_RDY_N);
  endsequence

  property NoDataAfterEOF;
     @(posedge CLK) disable iff (RESET) 
        (!EOF_N) && !(SRC_RDY_N || DST_RDY_N) |=> 
	   !(SOF_N && !(SRC_RDY_N || DST_RDY_N)) throughout sop_seq;
  endproperty

  assert property (NoDataAfterEOF)
     else $error("InternalBus transaction continued after EOF_N.");

  // -- Matching EOF after SOF ------------------------------------------------
  // Each SOF must be, after some time, followed by EOF. Each transaction must
  // have its end. First, we define a sequence of waiting for the first active
  // EOF. Then we declare, that after active cycle of SOF, there may be no
  // another active SOF during that sequence ( = until active EOF).
  sequence eop_seq;
     ##[0:$] (!EOF_N) && !(SRC_RDY_N || DST_RDY_N);
  endsequence

  property EOFMatchSOF;
     @(posedge CLK) disable iff (RESET) 
        (!SOF_N) && !(SRC_RDY_N || DST_RDY_N) |=>
           (!((!SOF_N) && !(SRC_RDY_N || DST_RDY_N))) throughout eop_seq;
  endproperty

  assert property (EOFMatchSOF)
     else $error("SOF_N was not followed by matching EOF_N after some time");


endinterface 



