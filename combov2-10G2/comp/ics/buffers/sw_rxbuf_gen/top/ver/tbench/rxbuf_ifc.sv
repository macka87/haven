/*
 * rxbuf_ifc.pkg: SW RX Buffer Interface
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
 * $Id: rxbuf_ifc.sv 13961 2010-06-07 11:21:51Z xkoran01 $
 *
 * TODO:
 *
 */
 
  import math_pkg::*;
// ----------------------------------------------------------------------------
//                         SW RX Buffer Interface declaration
// ----------------------------------------------------------------------------

// -- Sw Rx Buffer Interface -----------------------------------------------------
interface iSwRxBuffer #(DATA_WIDTH=64, BLOCK_SIZE=512, FLOWS=2) (input logic CLK, RESET);  
  // -- Write interface (FrameLinks)
    logic [DATA_WIDTH-1:0] RX_DATA       = 0;
    logic                  RX_SOP_N      = 1;
    logic                  RX_EOP_N      = 1;
    logic                  RX_SOF_N      = 1;
    logic                  RX_EOF_N      = 1;
    logic [log2(DATA_WIDTH/8)-1:0]   RX_REM     = 0;
    logic                  RX_SRC_RDY_N  = 1;
    logic                  RX_DST_RDY_N;
    
    // Belong to Write interface, but used on output (in monitor & responder)
    logic [15:0]   RX_NEWLEN;
    logic          RX_NEWLEN_DV;
    logic [abs(log2(FLOWS)-1):0]         RX_NEWLEN_IFC;  // always set to '1'
    logic [15:0]   RX_RELLEN     = 0;
    logic          RX_RELLEN_DV  = 0;
    logic [abs(log2(FLOWS)-1):0] RX_RELLEN_IFC;

  // -- Read interface (InternalBus)
    logic [31:0]           RD_ADDR       = 0;
    logic [((DATA_WIDTH/8)-1):0]            RD_BE         = 0;
    logic                  RD_REQ        = 0;
    logic                  RD_ARDY;

    logic [DATA_WIDTH-1:0] RD_DATA;
    logic                  RD_SRC_RDY;
    logic                  RD_DST_RDY    = 0;   

  clocking fl_cb @(posedge CLK);
    input  RX_DST_RDY_N;
    output RX_DATA, RX_SOP_N, RX_EOP_N, RX_SOF_N, RX_EOF_N, RX_REM, RX_SRC_RDY_N;  
  endclocking: fl_cb;
  
  clocking ib_cb @(posedge CLK);
    input  RD_DATA, RD_SRC_RDY, RD_ARDY, RD_ADDR, RD_BE, RD_REQ;
    output RD_DST_RDY;  
  endclocking: ib_cb;
  
  clocking monitor_cb @(posedge CLK);
    input  RD_DATA, RD_SRC_RDY, RD_ARDY, RD_DST_RDY, RD_BE, RX_NEWLEN, RX_NEWLEN_DV, RX_NEWLEN_IFC;
    output RD_ADDR, RD_REQ, RX_RELLEN, RX_RELLEN_DV, RX_RELLEN_IFC;
  endclocking: monitor_cb;

  // Receive Modport
  modport fl  (input  RX_DATA,
               input  RX_SOP_N,
               input  RX_EOP_N,
               input  RX_SOF_N,
               input  RX_EOF_N,
               input  RX_REM,
               input  RX_SRC_RDY_N,
               output RX_DST_RDY_N);
               
  // Transitive Modport
  modport ib  (output RD_DATA,
               output RD_SRC_RDY,
               input  RD_DST_RDY,
               input  RD_ADDR,
               input  RD_BE,
               input  RD_REQ,
               output RD_ARDY,
               output RX_NEWLEN,
               output RX_NEWLEN_DV,
               output RX_NEWLEN_IFC,
               input  RX_RELLEN,
               input  RX_RELLEN_DV,
               input  RX_RELLEN_IFC);
  
  // CB Modport
  modport fl_tb (clocking fl_cb);
  modport ib_tb (clocking ib_cb);
  modport monitor (clocking monitor_cb);

  // --------------------------------------------------------------------------
  // -- Interface properties/assertions
  // --------------------------------------------------------------------------

  // -- SOF together with SOP -------------------------------------------------
  // SOF may be active only if SOP is active. 
  
  property SOFSOP;
     @(posedge CLK) !(RX_SOF_N)|->!(RX_SOP_N); 
  endproperty   
  
  assert property (SOFSOP)
     else $error("RX_SOF_N is not active the same time as RX_SOP_N.");


  // -- EOF together with EOP -------------------------------------------------
  // EOF may be active only if EOP is active.
  
  property EOFEOP;
     @(posedge CLK) !(RX_EOF_N)|->!(RX_EOP_N); 
  endproperty    
  
  assert property (EOFEOP)
     else $error("RX_EOF_N is not active the same time as RX_EOP_N.");   


  // -- No data after EOP ----------------------------------------------------
  // After EOP, data cannot be sent, until SOP is sent. EOP marks end of
  // transaction. First, we define a sequence of waiting for the first active
  // SOP. Then we declare, that after active cycle of EOP, there may be no
  // transfer during that sequence ( = until active SOP).
  
  sequence sop_seq;
     ##[0:$] (!RX_SOP_N) && !(RX_SRC_RDY_N || RX_DST_RDY_N);
  endsequence

  property NoDataAfterEOP;
     @(posedge CLK) disable iff (RESET) 
        (!RX_EOP_N) && !(RX_SRC_RDY_N || RX_DST_RDY_N) |=> 
	   !(RX_SOP_N && !(RX_SRC_RDY_N || RX_DST_RDY_N)) throughout sop_seq;
  endproperty

  assert property (NoDataAfterEOP)
     else $error("FrameLink transaction continued after RX_EOP_N.");
     
endinterface : iSwRxBuffer
