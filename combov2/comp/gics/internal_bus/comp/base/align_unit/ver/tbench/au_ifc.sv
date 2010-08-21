/*
 * au_ifc.pkg: Align unit Interface
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
 * $Id: au_ifc.sv 3590 2008-07-16 09:05:59Z xsanta06 $
 *
 * TODO:
 *
 */
 

// ----------------------------------------------------------------------------
//                         Align Unit Interface declaration
// ----------------------------------------------------------------------------

// -- Align Unit Interface -----------------------------------------------------
interface iAlignUnit (input logic CLK, RESET);  
  //  -- Control interface ----------------------------------------------------    
  logic [2:0] SRC_ADDR      = 0; 
  logic [2:0] DST_ADDR      = 0; 
  logic [2:0] DATA_LEN      = 0;  

  //  -- Input interface ------------------------------------------------------
  logic [63:0] IN_DATA      = 0;   // Input Data
  logic IN_SOF              = 0;   // Start of Frame
  logic IN_EOF              = 0;   // End of Frame
  logic IN_SRC_RDY          = 0;   // Source data ready
  logic IN_DST_RDY             ;   // Destination data ready   

  //  -- Output interface -----------------------------------------------------
  logic [63:0] OUT_DATA        ;   // Output Data
  logic OUT_SOF                ;   // Start of Frame
  logic OUT_EOF                ;   // End of Frame    
  logic OUT_SRC_RDY            ;   // Source data ready  
  logic OUT_DST_RDY         = 0;   // Destination data ready   

  clocking rx_cb @(posedge CLK);
    input  IN_DST_RDY;
    output IN_DATA, IN_SOF, IN_EOF, IN_SRC_RDY, SRC_ADDR, DST_ADDR, DATA_LEN;  
  endclocking: rx_cb;
  
  clocking tx_cb @(posedge CLK);
    input  OUT_DATA, OUT_SOF, OUT_EOF, OUT_SRC_RDY;
    output OUT_DST_RDY;  
  endclocking: tx_cb;
  
  clocking monitor_cb @(posedge CLK);
    input  OUT_DATA, OUT_SOF, OUT_EOF, OUT_SRC_RDY, OUT_DST_RDY, DST_ADDR;
  endclocking: monitor_cb;

  // Receive Modport
  modport rx  (input  IN_DATA,
               input  IN_SOF,
               input  IN_EOF,
               input  IN_SRC_RDY,
               output IN_DST_RDY,
               input  SRC_ADDR,
               input  DST_ADDR,
               input  DATA_LEN
               );
               
  // Transitive Modport
  modport tx  (output OUT_DATA,
               output OUT_SOF,
               output OUT_EOF,
               output OUT_SRC_RDY,
               input  OUT_DST_RDY
               );
  
  // CB Modport
  modport rx_tb (clocking rx_cb);
  modport tx_tb (clocking tx_cb);
  modport monitor (clocking monitor_cb);

/*
  // --------------------------------------------------------------------------
  // -- Interface properties/assertions
  // --------------------------------------------------------------------------

  // -- No data after EOP ----------------------------------------------------
  // After EOP, data cannot be sent, until SOP is sent. EOP marks end of
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
     else $error("FrameLink transaction continued after EOP_N.");
     
*/     
endinterface : iAlignUnit
