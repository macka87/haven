/*
 * ib_ifc.sv: System Verilog Internal Bus interface
 * Copyright (C) 2009 CESNET
 * Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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
 * $Id: ib_ifc.sv 8319 2009-05-04 19:23:00Z washek $
 *
 * TODO:
 *
 */


// ----------------------------------------------------------------------------
//                        Interface declaration
// ----------------------------------------------------------------------------

// -- Internal Bus Interface Tx -----------------------------------------------
interface iInternalBusTx #(int DATA_WIDTH=64) (input logic CLK, RESET);
  
  logic [DATA_WIDTH-1:0] DATA;          // Data
  logic                  SOF_N;         // Start of Frame active in low
  logic                  EOF_N;         // End of Frame active in low
  logic                  SRC_RDY_N;     // Source data ready active in low
  logic                  DST_RDY_N;     // Destination data ready active in low
  
  
  //-- Clocking Block ---------------------------------------------------------
  clocking cb @(posedge CLK);
     input DATA, SOF_N, EOF_N, SRC_RDY_N;
     output DST_RDY_N;
  endclocking: cb
  
  //-- Modports ---------------------------------------------------------------
  modport dut (input  DST_RDY_N,
               output DATA, SOF_N, EOF_N, SRC_RDY_N
              );
  
  modport tb (clocking cb);
  
  
  // --------------------------------------------------------------------------
  // -- Interface properties/assertions
  // --------------------------------------------------------------------------

  // -- SOF together with EOF -------------------------------------------------
  // If data width < 128 bits, no SOF may be active together with EOF,
  //because no Internal Bus transaction is less than 128bits long.
  property NoSOFEOF;
     @(posedge CLK) disable iff (RESET !== 1'b0) SOF_N || EOF_N || SRC_RDY_N;
  endproperty
  
  if (DATA_WIDTH < 128)
     assert property (NoSOFEOF)
        else $error("SOF_N and EOF_N signals are active at the same cycle.");
  
  // -- No data after EOF ----------------------------------------------------
  // After EOF, no data cannot be sent, until SOF is sent. EOF marks end of
  // transaction. First, we define a sequence of waiting for the first active
  // SOF. Then we declare, that after active cycle of EOF, there may be no
  // transfer during that sequence ( = until active SOF).
  sequence sof_seq;
     ##[0:$] (!SOF_N) && !(SRC_RDY_N || DST_RDY_N);
  endsequence

  property NoDataAfterEOF;
     @(posedge CLK) disable iff (RESET !== 1'b0) 
        (!EOF_N) && !(SRC_RDY_N || DST_RDY_N) |=> 
	   !(SOF_N && !(SRC_RDY_N || DST_RDY_N)) throughout sof_seq;
  endproperty

  assert property (NoDataAfterEOF)
     else $error("InternalBus transaction continued after EOF_N.");

  // -- Matching EOF after SOF ------------------------------------------------
  // Each SOF must be, after some time, followed by EOF. Each transaction must
  // have its end. First, we define a sequence of waiting for the first active
  // EOF. Then we declare, that after active cycle of SOF, there may be no
  // another active SOF during that sequence ( = until active EOF).
  sequence eof_seq;
     ##[0:$] (!EOF_N) && !(SRC_RDY_N || DST_RDY_N);
  endsequence

  property EOFMatchSOF;
     @(posedge CLK) disable iff (RESET !== 1'b0) 
        (!SOF_N) && EOF_N && !(SRC_RDY_N || DST_RDY_N) |=>
           (!((!SOF_N) && !(SRC_RDY_N || DST_RDY_N))) throughout eof_seq;
  endproperty

  assert property (EOFMatchSOF)
     else $error("SOF_N was not followed by matching EOF_N after some time");

  // -- While RESET DST_RDY_N inactive ----------------------------------------
  // DST_RDY_N may be active only if RESET is inactive.
  property RESETDST;
     @(posedge CLK) (RESET)|->(DST_RDY_N !== 0); 
  endproperty
  
  assert property (RESETDST)
     else $error("DST_RDY_N is active during reset.");

endinterface




// -- Internal Bus Interface Rx -----------------------------------------------
interface iInternalBusRx #(int DATA_WIDTH=64) (input logic CLK, RESET);
  
  logic [DATA_WIDTH-1:0] DATA;          // Data
  logic                  SOF_N;         // Start of Frame active in low
  logic                  EOF_N;         // End of Frame active in low
  logic                  SRC_RDY_N;     // Source data ready active in low
  logic                  DST_RDY_N;     // Destination data ready active in low
  
  
  //-- Clocking Block ---------------------------------------------------------
  clocking cb @(posedge CLK);
     input DST_RDY_N;
     output DATA, SOF_N, EOF_N, SRC_RDY_N;
  endclocking: cb
  
  //-- Modports ---------------------------------------------------------------
  modport dut (input  DATA, SOF_N, EOF_N, SRC_RDY_N,
               output DST_RDY_N
              );
  
  modport tb (clocking cb);

  
  // --------------------------------------------------------------------------
  // -- Interface properties/assertions
  // --------------------------------------------------------------------------

  // -- SOF together with EOF -------------------------------------------------
  // If data width < 128 bits, no SOF may be active together with EOF,
  //because no Internal Bus transaction is less than 128bits long.
  property NoSOFEOF;
     @(posedge CLK) disable iff (RESET !== 1'b0) SOF_N || EOF_N || SRC_RDY_N;
  endproperty
  
  if (DATA_WIDTH < 128)
     assert property (NoSOFEOF)
        else $error("SOF_N and EOF_N signals are active at the same cycle.");
  
  // -- No data after EOF ----------------------------------------------------
  // After EOF, no data cannot be sent, until SOF is sent. EOF marks end of
  // transaction. First, we define a sequence of waiting for the first active
  // SOF. Then we declare, that after active cycle of EOF, there may be no
  // transfer during that sequence ( = until active SOF).
  sequence sof_seq;
     ##[0:$] (!SOF_N) && !(SRC_RDY_N || DST_RDY_N);
  endsequence

  property NoDataAfterEOF;
     @(posedge CLK) disable iff (RESET !== 1'b0) 
        (!EOF_N) && !(SRC_RDY_N || DST_RDY_N) |=> 
	   !(SOF_N && !(SRC_RDY_N || DST_RDY_N)) throughout sof_seq;
  endproperty

  assert property (NoDataAfterEOF)
     else $error("InternalBus transaction continued after EOF_N.");

  // -- Matching EOF after SOF ------------------------------------------------
  // Each SOF must be, after some time, followed by EOF. Each transaction must
  // have its end. First, we define a sequence of waiting for the first active
  // EOF. Then we declare, that after active cycle of SOF, there may be no
  // another active SOF during that sequence ( = until active EOF).
  sequence eof_seq;
     ##[0:$] (!EOF_N) && !(SRC_RDY_N || DST_RDY_N);
  endsequence

  property EOFMatchSOF;
     @(posedge CLK) disable iff (RESET !== 1'b0) 
        (!SOF_N) && EOF_N && !(SRC_RDY_N || DST_RDY_N) |=>
           (!((!SOF_N) && !(SRC_RDY_N || DST_RDY_N))) throughout eof_seq;
  endproperty

  assert property (EOFMatchSOF)
     else $error("SOF_N was not followed by matching EOF_N after some time");

  // -- While RESET DST_RDY_N inactive ----------------------------------------
  // DST_RDY_N may be active only if RESET is inactive.
  property RESETDST;
     @(posedge CLK) (RESET)|->(DST_RDY_N !== 0); 
  endproperty
  
  assert property (RESETDST)
     else $error("DST_RDY_N is active during reset.");

endinterface 
