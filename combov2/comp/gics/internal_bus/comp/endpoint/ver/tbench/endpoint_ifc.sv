/*
 * endpoint_ifc.sv: System Verilog Internal Bus Endpoint interface
 * Copyright (C) 2008 CESNET
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
 * $Id: endpoint_ifc.sv 8517 2009-05-28 10:55:58Z washek $
 *
 * TODO:
 *
 */


// ----------------------------------------------------------------------------
//                        Interface declaration
// ----------------------------------------------------------------------------

// -- IB Enpoint Write Interface ----------------------------------------------
interface iIbEndpointWrite #(int DATA_WIDTH=64, int ADDR_WIDTH=32)
                                                      (input logic CLK, RESET);
  logic                    REQ;
  logic                    RDY;
  logic [ADDR_WIDTH-1:0]   ADDR;
  logic [DATA_WIDTH-1:0]   DATA;
  logic [DATA_WIDTH/8-1:0] BE;
  logic [11:0]             LENGTH;
  logic                    SOF;
  logic                    EOF;
  
  //-- Clocking Blocks --
  clocking cb @(posedge CLK);
     input DATA, ADDR, BE, REQ, LENGTH, SOF, EOF;
     output RDY;
  endclocking: cb

  
  //-- Modports --
  modport dut (input  RDY,
               output DATA, ADDR, BE, REQ, LENGTH, SOF, EOF);
  
  modport tb  (clocking cb);
  
  
  //-- Properties and assertions --

  //Byte Enable only with SOF or EOF. 
  //It must be all ones between SOF and EOF.
  const logic [17-DATA_WIDTH/8-1:0] BEreaminder = 17'h1FFFF;
  property BE_SOF_EOF;
    @(posedge CLK) (REQ && !(SOF || EOF)) |-> {BEreaminder,BE} == 17'h1FFFF;
  endproperty
  
  if (DATA_WIDTH > 8)
    assert property (BE_SOF_EOF)
      else $error("BE are not all ones but SOF and EOF are inactive.");
  
  //Byte Enable mustn't be all zeroes
  property BE_not_zero;
    @(posedge CLK) REQ |-> BE != 0;
  endproperty
  
  if (DATA_WIDTH > 8)
    assert property (BE_not_zero)
      else $error("BE is all zeroes.");
  
  //No data after EOF.
  //After EOF, no data cannot be sent, until SOF is sent.
  sequence sof_seq;
     ##[0:$] SOF && REQ && RDY;
  endsequence

  property NoDataAfterEOF;
     @(posedge CLK) disable iff (RESET !== 1'b0) 
        EOF && REQ && RDY |=> !(REQ && !SOF) throughout sof_seq;
  endproperty

  assert property (NoDataAfterEOF)
     else $error("Memory write transaction continued after EOF.");
  
  //Matching EOF after SOF.
  //Each SOF must be followed by EOF after some time.
  sequence eof_seq;
     ##[0:$] EOF && REQ && RDY;
  endsequence

  property EOFMatchSOF;
     @(posedge CLK) disable iff (RESET !== 1'b0) 
        SOF && (!EOF) && REQ && RDY |=> !(SOF && REQ) throughout eof_seq;
  endproperty

  assert property (EOFMatchSOF)
     else $error("Two succesive SOFs without an EOF between them.");
  
endinterface


// -- IB Endpoint Read Interface ----------------------------------------------
interface iIbEndpointRead #(int DATA_WIDTH=64, int ADDR_WIDTH=32)
                                                      (input logic CLK, RESET);

  logic [ADDR_WIDTH-1:0]   ADDR;
  logic [DATA_WIDTH/8-1:0] BE;
  logic                    REQ;
  logic                    ARDY_ACCEPT;
  logic [11:0]             LENGTH;
  logic                    SOF;
  logic                    EOF;
  logic [DATA_WIDTH-1:0]   DATA;
  logic                    SRC_RDY;
  logic                    DST_RDY;
  
  //-- Clocking Blocks --
  clocking cb @(posedge CLK);
     input ADDR, BE, REQ, LENGTH, SOF, EOF, DST_RDY;
     output ARDY_ACCEPT, DATA, SRC_RDY;
  endclocking: cb

  
  //-- Modports --
  modport dut (input ARDY_ACCEPT, DATA, SRC_RDY,
               output ADDR, BE, REQ, LENGTH, SOF, EOF, DST_RDY);
  
  modport tb  (clocking cb);
  

  //-- Properties and assertions --

  //Byte Enable only with SOF or EOF. 
  //It must be all ones between SOF and EOF.
  const logic [17-DATA_WIDTH/8-1:0] BEreaminder = 17'h1FFFF;
  property BE_SOF_EOF;
    @(posedge CLK) (REQ && !(SOF || EOF)) |-> {BEreaminder,BE} == 17'h1FFFF;
  endproperty
  
  if (DATA_WIDTH > 8)
    assert property (BE_SOF_EOF)
      else $error("BE are not all ones when SOF and EOF are inactive.");
  
  //Byte Enable mustn't be all zeroes
  property BE_not_zero;
    @(posedge CLK) REQ |-> BE != 0;
  endproperty
  
  if (DATA_WIDTH > 8)
    assert property (BE_not_zero)
      else $error("BE is all zeroes.");
  
  //No data after EOF.
  //After EOF, no data cannot be sent, until SOF is sent.
  sequence sof_seq;
     ##[0:$] SOF && REQ && ARDY_ACCEPT;
  endsequence

  property NoDataAfterEOF;
     @(posedge CLK) disable iff (RESET !== 1'b0) 
        EOF && REQ && ARDY_ACCEPT |=> !(REQ && !SOF) throughout sof_seq;
  endproperty

  assert property (NoDataAfterEOF)
     else $error("Memory read transaction continued after EOF.");
  
  //Matching EOF after SOF.
  //Each SOF must be followed by EOF after some time.
  sequence eof_seq;
     ##[0:$] EOF && REQ && ARDY_ACCEPT;
  endsequence

  property EOFMatchSOF;
     @(posedge CLK) disable iff (RESET !== 1'b0) 
       SOF && (!EOF) && REQ && ARDY_ACCEPT |=> !(SOF && REQ) throughout eof_seq;
  endproperty

  assert property (EOFMatchSOF)
     else $error("Two succesive SOFs without an EOF between them.");

endinterface


// -- IB Endpoint Bus Master Done Interface -----------------------------------
interface iIbEndpointBMDone (input logic CLK, RESET);
  logic [7:0]            TAG;
  logic                  TAG_VLD;

  //-- Clocking Blocks
  clocking cb @(posedge CLK);
     input TAG, TAG_VLD;
  endclocking: cb

  //-- Modports
  modport dut (output TAG, TAG_VLD);

  modport tb (clocking cb);
  
endinterface
