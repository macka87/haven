/*
 * ddm_ifc.sv: Descriptor Download Manager Interface
 * Copyright (C) 2009 CESNET
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
 * $Id: ddm_ifc.sv 10987 2009-09-03 15:42:41Z xsimko03 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//             DDM Interface declaration
// ----------------------------------------------------------------------------

interface iDdm #(FLOWS=4, BLOCK_SIZE=4) (input logic CLK, RESET);  

  import math_pkg::*;       // log2()    
 
  //-- Signals ----------------------------------------------------------------  
                       
  // DDM misc interface
  logic [2*FLOWS-1:0]                RUN;                
  logic [2*FLOWS-1:0]                IDLE        = 0;
  logic [abs(log2(FLOWS*2))-1:0]     DMA_IFC;
  logic [2*FLOWS-1:0]                INIT;  
  // DDM RxReqFifo interface
  logic [abs(log2(FLOWS)-1):0]       RX_RF_ADDR;
  logic [log2(BLOCK_SIZE)+64:0]      RX_RF_DATA;
  logic                              RX_RF_DATA_VLD;
  logic [FLOWS-1:0]                  RX_RF_FULL  = 0;
  logic [FLOWS-1:0]                  RX_RF_INIT;
  // DDM RX nfifo to rx_dma_ctrl
  logic [63:0]                       RX_NFIFO_DOUT;
  logic                              RX_NFIFO_DOUT_VLD;
  logic [abs(log2(FLOWS)-1):0]       RX_NFIFO_RADDR = 0;
  logic                              RX_NFIFO_RD = 0;
  logic [FLOWS-1:0]                  RX_NFIFO_EMPTY;
  // DDM TX nfifo to tx_dma_ctrl
  logic [63:0]                       TX_NFIFO_DOUT;
  logic                              TX_NFIFO_DOUT_VLD;
  logic [abs(log2(FLOWS)-1):0]       TX_NFIFO_RADDR = 0;
  logic                              TX_NFIFO_RD = 0;
  logic [FLOWS-1:0]                  TX_NFIFO_EMPTY;

  //-- Clocking Blocks -------------------------------------------------------- 
  
  // Status Clocking Block 
    clocking misc_cb @(posedge CLK);
     input RUN, INIT, DMA_IFC;
     output IDLE;
    endclocking: misc_cb; 
    
  // DDM RxReqFifo Clocking Block 
    clocking rxreq_cb @(posedge CLK);
     input RX_RF_ADDR, RX_RF_DATA, RX_RF_DATA_VLD, RX_RF_INIT;
     output RX_RF_FULL;
    endclocking: rxreq_cb; 
   
  // RX nfifo Clocking Block 
    clocking rxnfifo_cb @(posedge CLK);
     input RX_NFIFO_DOUT, RX_NFIFO_DOUT_VLD, RX_NFIFO_EMPTY; 
     output RX_NFIFO_RADDR, RX_NFIFO_RD;
    endclocking: rxnfifo_cb; 
    
  // TX nfifo Clocking Block 
    clocking txnfifo_cb @(posedge CLK);
     input TX_NFIFO_DOUT, TX_NFIFO_DOUT_VLD, TX_NFIFO_EMPTY;
     output TX_NFIFO_RADDR, TX_NFIFO_RD;
    endclocking: txnfifo_cb; 
   
  //-- Modports ---------------------------------------------------------------
 
  // Misc Modport
    modport misc       (input  IDLE,
                        output RUN,
                        output INIT,
                        output DMA_IFC);
  // DDM RxReqFifo Modport
    modport rxreq      (input  RX_RF_FULL,
                        output RX_RF_ADDR,
                        output RX_RF_DATA,
                        output RX_RF_DATA_VLD,
                        output RX_RF_INIT);
  // RX nfifo Modport
    modport rxnfifo    (input  RX_NFIFO_RADDR,
                        input  RX_NFIFO_RD,
                        output RX_NFIFO_DOUT,
                        output RX_NFIFO_DOUT_VLD,
                        output RX_NFIFO_EMPTY);
                        
  // TX nfifo Modport
    modport txnfifo    (input  TX_NFIFO_RADDR,
                        input  TX_NFIFO_RD,
                        output TX_NFIFO_DOUT,
                        output TX_NFIFO_DOUT_VLD,
                        output TX_NFIFO_EMPTY);
                   
                       
  //-- TB Modports ----------------------------------------------------
   modport misc_tb   (clocking misc_cb);
   modport rxreq_tb   (clocking rxreq_cb);
   modport rxnfifo_tb (clocking rxnfifo_cb);
   modport txnfifo_tb (clocking txnfifo_cb);
   
  // --------------------------------------------------------------------------
  // -- DDM Interface properties/assertions
  // --------------------------------------------------------------------------

  // -- RX_NFIFO_RD together with not RX_NFIFO_EMPTY --------------------------------
  // RX_NFIFO_RD cannot be active together with RX_NFIFO_EMPTY for corresponding block.
  property RXREADNOTEMPTY;
     @(posedge CLK) disable iff (RESET)
       ($rose(RX_NFIFO_RD))|->(!RX_NFIFO_EMPTY[RX_NFIFO_RADDR]); 
  endproperty
  
  assert property (RXREADNOTEMPTY)
     else $error("RX_NFIFO_RD and RX_NFIFO_EMPTY for corresponding block signals are active at the same cycle.");  

  // -- TX_NFIFO_RD together with not TX_NFIFO_EMPTY --------------------------------
  // TX_NFIFO_RD cannot be active together with TX_NFIFO_EMPTY for corresponding block.
  property TXREADNOTEMPTY;
     @(posedge CLK) disable iff (RESET)
       ($rose(TX_NFIFO_RD))|->(!TX_NFIFO_EMPTY[TX_NFIFO_RADDR]); 
  endproperty
  
  assert property (TXREADNOTEMPTY)
     else $error("TX_NFIFO_RD and TX_NFIFO_EMPTY for corresponding block signals are active at the same cycle."); 
     
  // -- INIT = 1  min one clock after RUN = 0, IDLE have to be set to 1
      
  for (genvar i=0; i<8; i++) begin
    sequence init_seq;
      ##[0:$] (INIT[i] && IDLE[i]);
    endsequence;  

    property INITRUNIDLE;
       @(posedge CLK) 
         (!RUN[i]) |=> init_seq;
    endproperty
  
    assert property (INITRUNIDLE) 
      else $error("INIT is inactive after inactive RUN.");  
  end
endinterface : iDdm 

