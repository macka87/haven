/*
 * txbuffer_ifc.sv: Interface
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
 * $Id: txbuffer_ifc.sv 7853 2009-03-28 20:31:01Z xsimko03 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                         Interface declaration
// ----------------------------------------------------------------------------

// -- Tx Buffer Write Interface - Internal Bus --------------------------------
interface txBuffWrite #(DATA_WIDTH=64, BLOCK_SIZE=512, FLOWS=2, TOTAL_FLOW_SIZE=16384, SIZE_LENGTH=16) 
                       (input logic CLK, RESET);
  
  //-- Signals ----------------------------------------------
  
  logic [31:0]             WR_ADDR          = 0;            // Address          
  logic [7:0]              WR_BE            = 0;            // Byte Enable
  logic                    WR_REQ           = 0;            // Write Request
  logic                    WR_RDY;                          // Ready
  logic [DATA_WIDTH-1:0]   WR_DATA          = 0;            // Data
  
  logic [(FLOWS*16)-1:0]   TX_NEWLEN        = 0;            // Number of items to be marked as occuppied/valid     
  logic [FLOWS-1:0]        TX_NEWLEN_DV     = 0;            // Valid signal for TX_NEWLEN
  logic [FLOWS-1:0]        TX_NEWLEN_RDY;                   // Always set to '1'
  logic [(FLOWS*16)-1:0]   TX_RELLEN;                       // Number of items to be released   
  logic [FLOWS-1:0]        TX_RELLEN_DV;                    // Valid signal for TX_RELLEN
         
 
  //-- Clocking Blocks --------------------------------------- 
  
  // Clocking Block fifo_write 
     clocking txbuff_write_cb @(posedge CLK);
         input WR_RDY, TX_NEWLEN_RDY, TX_RELLEN, TX_RELLEN_DV;  
         output WR_ADDR, WR_BE, WR_REQ, WR_DATA, TX_NEWLEN, TX_NEWLEN_DV;
     endclocking: txbuff_write_cb;
 
  //-- Modports ----------------------------------------------
  
  // Internal Bus Write Modport
     modport writeBuff    (input  WR_ADDR,
                           input  WR_BE,
                           input  WR_REQ,
                           input  WR_DATA,
                           input  TX_NEWLEN,
                           input  TX_NEWLEN_DV,
                           output WR_RDY,
                           output TX_NEWLEN_RDY,
                           output TX_RELLEN,
                           output TX_RELLEN_DV);
                           
  //-- Transitive Modports -----------------------------------
  
     modport txbuff_write_tb (clocking txbuff_write_cb);                          
                           
endinterface : txBuffWrite     

// -- Tx Buffer Read Interface - Framelink ------------------------------------
interface txBuffRead #(TX_DATA_WIDTH=64, BLOCK_SIZE=512, FLOWS=2,  TOTAL_FLOW_SIZE=16384, SIZE_LENGTH=16) 
                      (input logic CLK, RESET);  
  
  import math_pkg::*;       // log2()                    
  
  //-- Signals ----------------------------------------------
  
  logic [TX_DATA_WIDTH-1:0]  TX_DATA;                       // Data
  logic TX_SOF_N;                                           // Start of Frame
  logic TX_SOP_N;                                           // Start of Packet
  logic TX_EOP_N;                                           // End of Packet
  logic TX_EOF_N;                                           // End of Frame
  logic [(log2(TX_DATA_WIDTH/8)-1):0] TX_REM;               // REM    
  logic TX_SRC_RDY_N;                                       // Source Ready
  logic TX_DST_RDY_N = 1;                                   // Destination Ready
  
  //-- Clocking Blocks --------------------------------------- 
  
  // Clocking Block fifo_write 
     
     clocking txbuff_read_cb @(posedge CLK);
         output TX_DST_RDY_N;
         input TX_DATA, TX_SOF_N, TX_SOP_N, TX_EOP_N, TX_EOF_N, TX_REM, TX_SRC_RDY_N;  
     endclocking: txbuff_read_cb;
  
     clocking monitor_cb @(posedge CLK);
         input TX_DATA, TX_SOF_N, TX_SOP_N, TX_EOP_N, TX_EOF_N, TX_REM, TX_SRC_RDY_N, TX_DST_RDY_N; 
     endclocking: monitor_cb;
  
  //-- Modports ----------------------------------------------
  
  // Framelink Read Modport
     modport readBuff     (input  TX_DST_RDY_N,
                           output TX_DATA,
                           output TX_SOF_N,
                           output TX_SOP_N,
                           output TX_EOP_N,
                           output TX_EOF_N,
                           output TX_REM,
                           output TX_SRC_RDY_N);
  //-- Transitive Modports -----------------------------------   
                        
     modport txbuff_read_tb (clocking txbuff_read_cb);
     modport monitor (clocking monitor_cb); 
     
 // --------------------------------------------------------------------------
  // -- Interface properties/assertions
  // --------------------------------------------------------------------------

  // -- While RESET SRC_RDY_N inactive ----------------------------------------
  // SRC_RDY_N may be active only if RESET is inactive. 
  
  /*property RESETSRC;
     @(posedge CLK) (RESET)|->(TX_SRC_RDY_N); 
  endproperty   
  
  assert property (RESETSRC)
     else $error("TX_SRC_RDY_N is active during reset.");*/
  
  // -- SOF together with SOP -------------------------------------------------
  // SOF may be active only if SOP is active. 
  
  property SOFSOP;
     @(posedge CLK) !(TX_SOF_N)|->!(TX_SOP_N); 
  endproperty   
  
  assert property (SOFSOP)
     else $error("SOF_N is not active the same time as TX_SOP_N.");


  // -- EOF together with EOP -------------------------------------------------
  // EOF may be active only if EOP is active.
  
  property EOFEOP;
     @(posedge CLK) !(TX_EOF_N)|->!(TX_EOP_N); 
  endproperty    
  
  assert property (EOFEOP)
     else $error("TX_EOF_N is not active the same time as TX_EOP_N.");   


  // -- No data after EOP ----------------------------------------------------
  // After EOP, data cannot be sent, until SOP is sent. EOP marks end of
  // transaction. First, we define a sequence of waiting for the first active
  // SOP. Then we declare, that after active cycle of EOP, there may be no
  // transfer during that sequence ( = until active SOP).
  
  sequence sop_seq;
     ##[0:$] (!TX_SOP_N) && !(TX_SRC_RDY_N || TX_DST_RDY_N);
  endsequence

  property NoDataAfterEOP;
     @(posedge CLK) disable iff (RESET) 
        (!TX_EOP_N) && !(TX_SRC_RDY_N || TX_DST_RDY_N) |=> 
	   !(TX_SOP_N && !(TX_SRC_RDY_N || TX_DST_RDY_N)) throughout sop_seq;
  endproperty

  assert property (NoDataAfterEOP)
     else $error("FrameLink transaction continued after TX_EOP_N.");                           
                           
endinterface : txBuffRead                                           
