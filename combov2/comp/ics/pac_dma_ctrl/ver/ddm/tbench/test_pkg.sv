  /*
   * test_pkg.sv: Test package
   * Copyright (C) 2009 CESNET
   * Author(s): Marcela Šimková <xsimko03@stud.fit.vutbr.cz>
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
   * $Id: test_pkg.sv 12303 2009-12-17 09:46:41Z kastovsky $
   *
   * TODO: Params for driver
   *
   */

  // ----------------------------------------------------------------------------
  //                        Package declaration
  // ----------------------------------------------------------------------------
  package test_pkg;
     
     import math_pkg::*;
     
     // common generics
     parameter FLOWS                      = 2;            // number of connected controllers
     parameter BASE_ADDR                  = 32'h00000000; // local base address
     parameter BLOCK_SIZE                 = 32;            // max number of descriptors in one transfer      
     parameter DMA_ID                     = 2'b00;        // tag for bus master operations
     parameter DMA_DATA_WIDTH             = 32;           // dma data width - output width of dma request
     parameter NFIFO_LUT_MEMORY           = 0;            // use lut memory type in nfifo
                                                       
     parameter BLOCK_LENGTH               = log2(BLOCK_SIZE)+1;
     parameter TRANS_TYPE                 = 0;
     parameter DATA_WIDTH                 = 64;           // IB data width
     
     // RING PARAMETERS
     parameter RING_PART_SIZE             = 512;          // number of descriptors in one part
     parameter RING_PARTS                 = 4;            // number of parts for each flow
       
     // CLOCKS AND RESETS
     parameter CLK_PERIOD = 10ns;
     parameter RESET_TIME = 10*CLK_PERIOD;

     // TXDRIVER0 PARAMETERS
     // vaha delay enable medzi transakciami         
     parameter TXDRIVER0_DELAYEN_WT         = 1;
     // vaha delay disable medzi transakciami                     
     parameter TXDRIVER0_DELAYDIS_WT        = 1;  
     // spodna hranica delay medzi transakciami                   
     parameter TXDRIVER0_DELAYLOW           = 0; 
     // horna hranica delay medzi transakciami                    
     parameter TXDRIVER0_DELAYHIGH          = 50; 
              
     // RXDRIVER0 PARAMETERS
     // vaha delay enable medzi transakciami         
     parameter RXDRIVER0_DELAYEN_WT         = 1;
     // vaha delay disable medzi transakciami                     
     parameter RXDRIVER0_DELAYDIS_WT        = 1;  
     // spodna hranica delay medzi transakciami                   
     parameter RXDRIVER0_DELAYLOW           = 0; 
     // horna hranica delay medzi transakciami                    
     parameter RXDRIVER0_DELAYHIGH          = 50; 
              

   /*// MONITOR0 PARAMETERS
   // Monitor data width
   parameter MONITOR0_DATA_WIDTH         = BUFFER_DATA_WIDTH;
   // Weight of delay enable between transactions          
   parameter MONITOR0_DELAYEN_WT         = 1;  
   // Weight of delay disable between transactions                  
   parameter MONITOR0_DELAYDIS_WT        = 3; 
   // Low boundary delay between transactions                    
   parameter MONITOR0_DELAYLOW           = 0; 
   // High boundary delay between transactions                    
   parameter MONITOR0_DELAYHIGH          = 3; 
   // Weight of delay enable in transaction                      
   parameter MONITOR0_INSIDE_DELAYEN_WT  = 1; 
   // Weight of delay disable in transaction                   
   parameter MONITOR0_INSIDE_DELAYDIS_WT = 3; 
   // Low boundary delay in transaction                    
   parameter MONITOR0_INSIDE_DELAYLOW    = 0; 
   // High boundary delay in transaction                    
   parameter MONITOR0_INSIDE_DELAYHIGH   = 3; */                    

   // TEST PARAMETERS
   parameter TRANSACTION_COUNT = 50000; // Count of transactions to generate

endpackage
