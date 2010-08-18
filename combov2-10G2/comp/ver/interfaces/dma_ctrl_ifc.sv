/*
 * tx_dma_ctrl__ifc.sv: Interface
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
 * $Id: dma_ctrl_ifc.sv 8569 2009-06-01 12:04:50Z xsimko03 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                    TX DMA Controller Interface declaration
// ----------------------------------------------------------------------------

// -- DMA Controller Interface ---------------------------------------------
interface iDmaCtrl #(CTRL_DMA_DATA_WIDTH=16) (input logic CLK, RESET);  

  import math_pkg::*;       // log2()    

  //-- Signals ----------------------------------------------------------------  
  // Misc Signals
  logic                                         INTERRUPT;
    
  // Descriptor FIFO interface
  logic                                         DESC_READ;
  logic [CTRL_DMA_DATA_WIDTH-1:0]               DESC_DO;                 
  logic                                         DESC_EMPTY;              
  logic                                         DESC_ENABLE;   // enable signal for controller
  
  // DMA Interface
  logic [log2(128/CTRL_DMA_DATA_WIDTH)-1:0]     DMA_ADDR;
  logic [CTRL_DMA_DATA_WIDTH-1:0]               DMA_DOUT;
  logic                                         DMA_REQ;
  logic                                         DMA_ACK;
  logic                                         DMA_DONE;
  logic [15:0]                                  DMA_TAG;
  
      
  //-- Clocking Blocks -------------------------------------------------------- 
  
  // Misc Clocking Block 
   clocking misc_cb @(posedge CLK);
     input INTERRUPT;
   endclocking: misc_cb;  
  
  // Descriptor Clocking Block 
   clocking desc_cb @(posedge CLK);
     input DESC_READ, DESC_ENABLE;  
     output DESC_DO, DESC_EMPTY;
   endclocking: desc_cb; 
     
  // DMA Clocking Block 
   clocking dma_cb @(posedge CLK);
     input DMA_DOUT, DMA_REQ;  
     output DMA_ADDR, DMA_ACK, DMA_DONE, DMA_TAG;
   endclocking: dma_cb;    
  

  //-- Modports ---------------------------------------------------------------
 
  // Misc Modport
   modport misc       (output INTERRUPT);
  
  // Descriptor Modport
   modport descriptor (output DESC_READ,
                       input  DESC_DO,
                       input  DESC_EMPTY,
                       output DESC_ENABLE);
                           
  // DMA Modport
   modport dma        (input  DMA_ADDR,
                       output DMA_DOUT,
                       output DMA_REQ,
                       input  DMA_ACK,
                       input  DMA_DONE,
                       input  DMA_TAG);                     
                           
  //-- TB Modports ----------------------------------------------------
   modport misc_tb (clocking misc_cb);
   modport desc_tb (clocking desc_cb);
   modport dma_tb  (clocking dma_cb);
    
  // --------------------------------------------------------------------------
  // -- Descriptor Manager Interface properties/assertions
  // --------------------------------------------------------------------------

  // -- Matching DESC_ENABLE after DESC_READ ----------------------------------
  // Each DESC_READ must be, after some time, followed by DESC_ENABLE. First, we 
  // define a sequence of waiting for the first active DESC_ENABLE. Then we 
  // declare, that DESC_READ must be active during that sequence 
  // ( = until active DESC_ENABLE).

  sequence descenable_seq;
    ##[0:$] (DESC_ENABLE);
  endsequence

  property ENABLEMatchREAD;
    @(posedge CLK) disable iff (RESET)
      (DESC_READ) && (!DESC_ENABLE)|=>
         (DESC_READ) throughout descenable_seq;
  endproperty
  
  assert property (ENABLEMatchREAD)  
    else $error("DESC_ENABLE is not active after DESC_READ!");
    
  // --------------------------------------------------------------------------
  // -- DMA Interface properties/assertions
  // --------------------------------------------------------------------------
  
  // -- Matching DMA_ACK after DMA_REQ ----------------------------------
  // Each DMA_REQ must be, after some time, followed by DMA_ACK. First, we 
  // define a sequence of waiting for the first active DMA_ACK. Then we 
  // declare, that DMA_REQ can not be active during that sequence 
  // ( = until active DMA_ACK).

  sequence dmaack_seq;
    ##[0:$] (DMA_ACK);
  endsequence

  property ACKMatchREQ;
    @(posedge CLK) disable iff (RESET)
      (DMA_REQ) && (!DMA_ACK)|=>
         (!DMA_REQ) throughout dmaack_seq;
  endproperty
  
  assert property (ACKMatchREQ)  
    else $error("DMA_ACK is not active after DMA_REQ!");  

endinterface : iDmaCtrl  