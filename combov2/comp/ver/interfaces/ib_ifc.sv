/*
 * ib_ifc.sv: Internal Bus Interface
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
 * $Id: ib_ifc.sv 8570 2009-06-01 12:05:27Z xsimko03 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                    Internal Bus Interface declaration
// ----------------------------------------------------------------------------

// -- Internal Bus Interface --------------------------------------------------
interface iInternalBus #(DATA_WIDTH=64) (input logic CLK, RESET);   

  // Write signals
  logic [31:0]                WR_ADDR;    
  logic [7:0]                 WR_BE;
  logic                       WR_REQ;
  logic                       WR_RDY;
  logic [DATA_WIDTH-1:0]      WR_DATA;
  
  // Read signals 
  logic [31:0]                RD_ADDR;    
  logic [7:0]                 RD_BE;
  logic                       RD_REQ;
  logic                       RD_ARDY;
  logic [DATA_WIDTH-1:0]      RD_DATA;
  logic                       RD_SRC_RDY;
  logic                       RD_DST_RDY;
  
    
  //-- Clocking Blocks --------------------------------------------------------    
   // IB Write Clocking Block
   clocking ib_write_cb @(posedge CLK);
     input WR_RDY;  
     output WR_ADDR, WR_BE, WR_REQ, WR_DATA;
   endclocking: ib_write_cb; 

   // IB Read Clocking Block
   clocking ib_read_cb @(posedge CLK);
     input RD_ARDY, RD_DATA, RD_SRC_RDY;  
     output RD_ADDR, RD_BE, RD_REQ, RD_DST_RDY;
   endclocking: ib_read_cb; 

  //-- Modports ---------------------------------------------------------------   
   // IB Write Modport
   modport ib_write (input  WR_ADDR,
                     input  WR_BE,
                     input  WR_REQ, 
                     output WR_RDY,
                     input  WR_DATA); 
                     
   // IB Read Modport
   modport ib_read  (input  RD_ADDR,
                     input  RD_BE,
                     input  RD_REQ, 
                     output RD_ARDY,
                     output RD_DATA,
                     output RD_SRC_RDY,
                     input  RD_DST_RDY);                                          
                           
  //-- Modports ---------------------------------------------------------------
   modport ib_write_tb (clocking ib_write_cb);    
   modport ib_read_tb (clocking ib_read_cb);
   
  // --------------------------------------------------------------------------
  // -- InternalBus Interface properties/assertions
  // -------------------------------------------------------------------------- 
  
  // -- RD_REQ together with RD_ARDY ------------------------------------------
  // RD_REQ must be active together with RD_ARDY.
  property REQARDY;
     @(posedge CLK) (RD_REQ)|->(RD_ARDY); 
  endproperty
  
  assert property (REQARDY)
     else $error("RD_REQ and RD_ARDY signals are not active at the same cycle.");
  
  // -- Matching RD_SRC_RDY together with RD_DST_RDY after RD_REQ -------------
  // Each RD_REQ must be, after some time, followed by RD_SRC_RDY together with 
  // RD_DST_RDY. First, we define a sequence of waiting for the first active 
  // RD_SRC_RDY together with RD_DST_RDY. Then we declare, that RD_REQ can not be 
  // active during that sequence.

  sequence srcdst_seq;
    ##[0:$] (RD_SRC_RDY)&&(RD_DST_RDY);
  endsequence

  property SRCDSTMatchREQ;
    @(posedge CLK) disable iff (RESET)
      (RD_REQ) && (!RD_SRC_RDY)|=>
         (!RD_REQ) throughout srcdst_seq;
  endproperty
  
  assert property (SRCDSTMatchREQ)  
    else $error("RD_SRC_RDY and RD_DST_RDY are not active together after RD_REQ!");
    
  // -- WR_REQ together with WR_RDY ------------------------------------------
  // RD_REQ must be active together with RD_ARDY.
  property REQRDY;
     @(posedge CLK) (WR_REQ)|->(WR_RDY); 
  endproperty
  
  assert property (REQRDY)
     else $error("WR_REQ and WR_RDY signals are not active at the same cycle.");  

endinterface : iInternalBus  


interface iInternalBusUp #(DATA_WIDTH=64) (input logic CLK, RESET);   

  // Internal Bus signals
  logic [DATA_WIDTH-1:0] DATA         ; // Data
  logic                  SOP_N        ; // Start of Packet active in low
  logic                  EOP_N        ; // End of Packet active in low
  logic                  SRC_RDY_N    ; // Source data ready active in low
  logic                  DST_RDY_N = 1; // Destination data ready active in low
    
  //-- Clocking Blocks --------------------------------------------------------   
   // IB Upstream Clocking Block
   clocking ib_up_cb @(posedge CLK);
     input DATA, SOP_N, EOP_N, SRC_RDY_N;
     output DST_RDY_N;
   endclocking: ib_up_cb;  
   
  //-- Modports ---------------------------------------------------------------
   // IB Upstream Modport
   modport ib_up    (output DATA,
                     output SOP_N,
                     output EOP_N,
                     output SRC_RDY_N,
                     input  DST_RDY_N); 
                     
  //-- Modports ---------------------------------------------------------------
   modport ib_up_tb (clocking ib_up_cb);  
   
   
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
   
endinterface : iInternalBusUp   


interface iInternalBusDown #(DATA_WIDTH=64) (input logic CLK, RESET);   

  // Internal Bus signals
  logic [DATA_WIDTH-1:0] DATA      = 0; // Data
  logic                  SOP_N     = 1; // Start of Packet active in low
  logic                  EOP_N     = 1; // End of Packet active in low
  logic                  SRC_RDY_N = 1; // Source data ready active in low
  logic                  DST_RDY_N    ; // Destination data ready active in low
    
  //-- Clocking Blocks --------------------------------------------------------   
   // IB Downstream Clocking Block
   clocking ib_down_cb @(posedge CLK);
     input DST_RDY_N;
     output DATA, SOP_N, EOP_N, SRC_RDY_N;
   endclocking: ib_down_cb;  
   
  //-- Modports ---------------------------------------------------------------
   // IB Downstream Modport
   modport ib_down  (input  DATA,
                     input  SOP_N,
                     input  EOP_N,
                     input  SRC_RDY_N,
                     output DST_RDY_N);
                     
  //-- Modports ---------------------------------------------------------------
   modport ib_down_tb (clocking ib_down_cb);
   
   
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
 
endinterface : iInternalBusDown                   
