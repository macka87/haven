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
   parameter FLOWS                      = 2;            // number of rx channels
   // RX BUFFER generics
   parameter BUFFER_DATA_WIDTH          = 64;           // Internal Bus data width
   parameter BUFFER_BLOCK_SIZE          = 512;          // available space in the RX buffer for each flow      
   parameter BUFFER_TOTAL_FLOW_SIZE     = 16384;        // total size [bytes] for one flow (interface)
   // RX CTRL generics
   parameter CTRL_BUFFER_ADDR           = 32'h00000000; // address of first rx buffer
   parameter CTRL_BUFFER_GAP            = 32'h00004000; // address gap between two rx buffers
   parameter CTRL_BUFFER_SIZE           = 4096;         // size of rx buffer
   parameter CTRL_DMA_ID                = 2'b10;        // tag for bus master operations
   parameter CTRL_DMA_DATA_WIDTH        = 64;           // dma data width - output width of dma request
   parameter CTRL_BLOCK_SIZE            = 32;            // size of inner fifo
   
   parameter RAM_SIZE                   = 19000;         // Size of RAM = RAM_SIZE*64b
   parameter MAX_SIZE_OF_PACKET         = 1520;
   parameter NUM_FLAGS                  = 8;
   parameter TRANS_TYPE                 = 1;
                                              
   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TESTBENCH PARAMETERS
   parameter RXDWIDTH    = BUFFER_DATA_WIDTH/FLOWS;
   parameter RXDREMWIDTH = log2(RXDWIDTH/8);
   
   // TRANSACTION FORMAT
   parameter GENERATOR_PACKET_COUNT      = 1;         // Number of packets in one frame
   int       GENERATOR_PACKET_SIZE_MAX[] = '{128};   // Max size of packets
   int       GENERATOR_PACKET_SIZE_MIN[] = '{64};     // Min size of packets
   
   // DRIVER0 PARAMETERS
   // datova sirka driveru
   parameter DRIVER0_DATA_WIDTH         = RXDWIDTH;
   // drem sirka driveru         
   parameter DRIVER0_DREM_WIDTH         = RXDREMWIDTH;
   // vaha delay enable medzi transakciami         
   parameter DRIVER0_DELAYEN_WT         = 1;
   // vaha delay disable medzi transakciami                     
   parameter DRIVER0_DELAYDIS_WT        = 3;  
   // spodna hranica delay medzi transakciami                   
   parameter DRIVER0_DELAYLOW           = 0; 
   // horna hranica delay medzi transakciami                    
   parameter DRIVER0_DELAYHIGH          = 3; 
   // vaha delay enable v transakcii                    
   parameter DRIVER0_INSIDE_DELAYEN_WT  = 1;
   // vaha delay disable v transakcii                     
   parameter DRIVER0_INSIDE_DELAYDIS_WT = 3;  
   // spodna hranica delay v transakcii                   
   parameter DRIVER0_INSIDE_DELAYLOW    = 0; 
   // horna hranica delay v transakcii                    
   parameter DRIVER0_INSIDE_DELAYHIGH   = 3;                    

   // MONITOR0 PARAMETERS
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
   parameter MONITOR0_INSIDE_DELAYHIGH   = 3;                     

   // TEST PARAMETERS
   parameter TRANSACTION_COUNT = 1000; // Count of transactions to generate

endpackage
