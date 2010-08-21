/*
 * pac_dma_ctrl_ifc.sv: Interface
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
 * $Id: pac_dma_ctrl_ifc.sv 11185 2009-09-15 09:50:13Z xsimko03 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//             DMA Interface declaration
// ----------------------------------------------------------------------------
`define NUM_FLAGS 8  // NUM_FLAGS parameter

interface iPacDmaCtrl #(FLOWS=4) (input logic CLK, RESET);  

  import math_pkg::*;       // log2()    
 
  //-- Signals ----------------------------------------------------------------  
                       
  // DMA misc interface
  logic [FLOWS-1:0]                  RUN         = 0;                 
  logic [FLOWS-1:0]                  IDLE;          
  logic [15:0]                       SETUP_SIG   = 0; 
  // Descriptor FIFO interface
  logic                              DESC_READ;
  logic [log2(FLOWS)-1:0]            DESC_ADDR;
  logic [63:0]                       DESC_DO     = 0;
  logic [FLOWS-1:0]                  DESC_EMPTY  = 0;
  logic                              DESC_DO_VLD = 0;
  // Status Update Manager interface
  logic [log2(FLOWS)-1:0]            SU_ADDR;
  logic [`NUM_FLAGS+16-1:0]          SU_DATA_RX;
  logic [`NUM_FLAGS-1:0]             SU_DATA_TX;
  logic                              SU_DATA_VLD;             
  logic [FLOWS-1:0]                  SU_HFULL    = 0;

  //-- Clocking Blocks -------------------------------------------------------- 
  
  // Status Clocking Block 
    clocking misc_cb @(posedge CLK);
     input IDLE;
     output RUN;
    endclocking: misc_cb; 

  // Setup Clocking Block
    clocking setup_cb @(posedge CLK);
     output SETUP_SIG; 
    endclocking: setup_cb;
    
  // Descriptor Clocking Block 
    clocking desc_cb @(posedge CLK);
     input DESC_READ, DESC_ADDR;
     output DESC_DO, DESC_EMPTY, DESC_DO_VLD;
    endclocking: desc_cb; 
   
  // RX Status Clocking Block 
    clocking statrx_cb @(posedge CLK);
     input SU_ADDR, SU_DATA_RX, SU_DATA_VLD;
     output SU_HFULL;
    endclocking: statrx_cb; 
    
  // TX Status Clocking Block 
    clocking stattx_cb @(posedge CLK);
     input SU_ADDR, SU_DATA_TX, SU_DATA_VLD;
     output SU_HFULL;
    endclocking: stattx_cb;  
   
  //-- Modports ---------------------------------------------------------------
 
  // Misc Modport
    modport misc       (output IDLE,
                        input  RUN);

  // Setup Modport     
    modport setup      (input  SETUP_SIG);

  // Descriptor Modport
    modport descriptor (output DESC_READ,
                        output DESC_ADDR,
                        input  DESC_DO,
                        input  DESC_EMPTY,
                        input  DESC_DO_VLD);
  // RX Status Update Modport
    modport statusrx   (output SU_ADDR,
                        output SU_DATA_RX,
                        output SU_DATA_VLD,
                        input  SU_HFULL);
                        
  // TX Status Update Modport
    modport statustx   (output SU_ADDR,
                        output SU_DATA_TX,
                        output SU_DATA_VLD,
                        input  SU_HFULL);                      
                       
  //-- TB Modports ----------------------------------------------------
   modport misc_tb   (clocking misc_cb);
   modport setup_tb  (clocking setup_cb);
   modport desc_tb   (clocking desc_cb);
   modport statrx_tb (clocking statrx_cb);
   modport stattx_tb (clocking stattx_cb);
   
  // --------------------------------------------------------------------------
  // -- DescMan Interface properties/assertions
  // --------------------------------------------------------------------------
  
  // -- DESC_READ together with not DESC_EMPTY --------------------------------
  // DESC_READ cannot be active together with DESC_EMPTY for corresponding block.
  property READNOTEMPTY;
     @(posedge CLK) disable iff (RESET)
       ($rose(DESC_READ))|->(!DESC_EMPTY[DESC_ADDR]); 
  endproperty
  
  assert property (READNOTEMPTY)
     else $error("DESC_READ and DESC_EMPTY for corresponding block signals are active at the same cycle.");  
 
  endinterface : iPacDmaCtrl 
  
