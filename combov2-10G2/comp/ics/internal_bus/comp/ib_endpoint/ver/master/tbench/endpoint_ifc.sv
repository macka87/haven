/*
 * endpoint_ifc.pkg: System Verilog Internal Bus Endpoint interface
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
 * $Id: endpoint_ifc.sv 333 2007-09-05 20:07:59Z xkobie00 $
 *
 * TODO:
 *
 */


// ----------------------------------------------------------------------------
//                        Interface declaration
// ----------------------------------------------------------------------------

// -- Internal Bus Write Interface --------------------------------------------
interface iIbEndpointWrite64 (input logic CLK, RESET);
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
interface iIbEndpointRead64s (input logic CLK, RESET);
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
