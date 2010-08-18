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
 * $Id: desc_manager_ifc.sv 4517 2008-08-07 11:58:17Z xsimko03 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                         Interface declaration
// ----------------------------------------------------------------------------

// -- Descriptor Manager Write Interface --------------------------------------
interface descManagerWrite #(BASE_ADDR=32'h0000000, FLOWS=32, BLOCK_SIZE=32) 
                            (input logic CLK, RESET);
  
  //-- Signals ----------------------------------------------
  // Write Interface
  logic [31:0]             WR_ADDR          = 0;            // Address          
  logic [7:0]              WR_BE            = 0;            // Byte Enable
  logic                    WR_REQ           = 0;            // Write Request
  logic                    WR_RDY;                          // Ready
  logic [63:0]             WR_DATA          = 0;            // Data
  
  // BM Interface
  logic [63:0]             BM_GLOBAL_ADDR;                  // Global Address in RAM
  logic [31:0]             BM_LOCAL_ADDR;                   // Local Address in FPGA
  logic [11:0]             BM_LENGTH;                       // Legth of Data 
  logic                    BM_REQ;                          // Request
  logic                    BM_ACK           = 0;            // Acknowledge after 3 takts
  
  // Per channel enable interface
  logic [FLOWS-1:0]        ENABLE           = 0;            // Enable signal  
  
  //-- Clocking Blocks --------------------------------------- 
  
     clocking writeDesc_cb @(posedge CLK);
          input WR_RDY, BM_GLOBAL_ADDR, BM_LOCAL_ADDR, BM_LENGTH, BM_REQ;  
          output WR_ADDR, WR_BE, WR_REQ, WR_DATA, BM_ACK, ENABLE;
     endclocking: writeDesc_cb;   
  
  //-- Modports ----------------------------------------------
  
  // Internal Bus Write Modport
     modport writeDesc    (input  WR_ADDR,
                           input  WR_BE,
                           input  WR_REQ,
                           input  WR_DATA,
                           input  BM_ACK,
                           input  ENABLE,
                           output WR_RDY,
                           output BM_GLOBAL_ADDR,
                           output BM_LOCAL_ADDR,
                           output BM_LENGTH,
                           output BM_REQ);
                           
  //-- Transitive Modports -----------------------------------
     modport writeDesc_tb (clocking writeDesc_cb); 
  
  // --------------------------------------------------------------------------
  // -- Interface properties/assertions
  // --------------------------------------------------------------------------

  // -- While RESET SRC_RDY_N inactive ----------------------------------------
  // SRC_RDY_N may be active only if RESET is inactive. 
  
  /*property DESC_NO_1;
     @(posedge CLK) (WR_REQ)|->(WR_DATA[0]==0); 
  endproperty   
  
  assert property (DESC_NO_1)
     else $error("Descriptor type 1.");*/
     
endinterface : descManagerWrite     

// -- Descriptor Manager Read Interface ---------------------------------------
interface descManagerRead #(BASE_ADDR=32'h00000000, FLOWS=32, BLOCK_SIZE=32) 
                           (input logic CLK, RESET);  
  
  //-- Signals ----------------------------------------------
  
  // DMA ctrls interface
  logic [(64/FLOWS)-1:0]   DATA_OUT;                        // Output Data
  logic                    EMPTY;                           // Empty signal
  logic                    READ             = 0;            // Read Signal
  
  //-- Clocking Blocks --------------------------------------- 
    
     clocking readDesc_cb @(posedge CLK);
          output READ;
          input  DATA_OUT, EMPTY;
     endclocking: readDesc_cb;
  
     clocking monitor_cb @(posedge CLK);
          input  READ, DATA_OUT, EMPTY;
     endclocking: monitor_cb;
  
   
       
  //-- Modports ----------------------------------------------
  
  // Framelink Read Modport
     modport readDesc     (input  READ,
                           output DATA_OUT,
                           output EMPTY);
  
  //-- Transitive Modports -----------------------------------   
     modport readDesc_tb (clocking readDesc_cb);
     modport monitor     (clocking monitor_cb);
                        
endinterface : descManagerRead                                           
