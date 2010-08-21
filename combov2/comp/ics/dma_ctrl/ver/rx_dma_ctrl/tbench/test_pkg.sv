/*
 * test_pkg.sv: Test package
 * Copyright (C) 2008 CESNET
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
 * $Id: test_pkg.sv 8583 2009-06-01 14:33:57Z xsimko03 $
 *
 * TODO: Params for driver
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package test_pkg;
   
   import math_pkg::*;
   
   // DUT GENERICS
   parameter BUFFER_DATA_WIDTH      = 64;       // RX buffer data width
   parameter BUFFER_BLOCK_SIZE      = 512;      // Max number of items in one block in
                                                // the RX buffer (for one flow)   
   parameter BUFFER_FLOWS           = 4;        // Number of flows in the RX buffer
   parameter BUFFER_TOTAL_FLOW_SIZE = 8192;     // (or 4096) Total size (in bytes) in the RX buffer for
                                                // one flow (interface)
   parameter CTRL_BUFFER_ADDR       = 0;        // Base address of the RX buffer
   parameter CTRL_DMA_DATA_WIDTH    = 8;       // Data width of DMA requests
   parameter PAGE_SIZE              = 4096;     // Size of page
   parameter PAGE_COUNT             = 2;        // Number of pages in RAM, should by power of 2            
   
   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TESTBENCH PARAMETERS
   parameter RXDWIDTH    = BUFFER_DATA_WIDTH/BUFFER_FLOWS;
   parameter RXDREMWIDTH = log2(RXDWIDTH/8);
   
   // TRANSACTION FORMAT
   parameter GENERATOR_PACKET_COUNT      = 2;           // Number of packets in one frame
   int       GENERATOR_PACKET_SIZE_MAX[] = '{32, 32};   // Max size of packets
   int       GENERATOR_PACKET_SIZE_MIN[] = '{0, 1};     // Min size of packets
   
   // DRIVER0 PARAMETERS
   // Driver data width
   parameter DRIVER0_DATA_WIDTH         = RXDWIDTH;
   // Weight of delay enable between transactions       
   parameter DRIVER0_DELAYEN_WT         = 1;
   // Weight of delay disable between transactions                     
   parameter DRIVER0_DELAYDIS_WT        = 0;  
   // Low boundary delay between transactions                   
   parameter DRIVER0_DELAYLOW           = 0; 
   // Hihg boundary delay between transactions                    
   parameter DRIVER0_DELAYHIGH          = 3; 
   // Weight of delay enable in transaction                    
   parameter DRIVER0_INSIDE_DELAYEN_WT  = 1;
   // Weight of delay disable in transaction                     
   parameter DRIVER0_INSIDE_DELAYDIS_WT = 3;  
   // Low boundary delay in transaction                   
   parameter DRIVER0_INSIDE_DELAYLOW    = 0; 
   // High boundary delay in transaction                    
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
