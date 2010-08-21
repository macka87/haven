/*
 * test_pkg.sv: Test package
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
 * $Id: test_pkg.sv 8584 2009-06-01 14:39:20Z xsimko03 $
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
   parameter BUFFER_DATA_WIDTH      = 64;       // TX buffer data width
   parameter BUFFER_BLOCK_SIZE      = 512;      // Max number of items in one block in
                                                // the TX buffer (for one flow)   
   parameter BUFFER_FLOWS           = 4;        // Number of flows in the TX buffer
   parameter BUFFER_TOTAL_FLOW_SIZE = 16384;    // Total size (bytes) in the TX buffer for
                                                // one flow (interface)
   parameter BUFFER_SIZE_LENGTH     = 16;       // length of one size in used protocol
   parameter BUFFER_USE_FL_PIPE     = 1;        // should the output of the TX buffer
                                                // registered? (1 = true, 0 = false)
   parameter CTRL_BUFFER_ADDR       = 0;        // Base address of the TX buffer
   parameter CTRL_DMA_DATA_WIDTH    = 8;       // Data width of DMA requests
   
   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TESTBENCH PARAMETERS
   parameter TXDWIDTH    = BUFFER_DATA_WIDTH/BUFFER_FLOWS;
   parameter TXDREMWIDTH = log2(TXDWIDTH/8);
   
   // TRANSACTION FORMAT
   parameter GENERATOR_PACKET_COUNT      = 2;           // Number of packets in one frame
   int       GENERATOR_PACKET_SIZE_MAX[] = '{32,1530};  // Max size of packets
   int       GENERATOR_PACKET_SIZE_MIN[] = '{0,1};     // Min size of packets
   
   // DRIVER0 PARAMETERS
   // Driver's data width
   parameter DRIVER0_DATA_WIDTH         = BUFFER_DATA_WIDTH;
   // Page count for one flow         
   parameter DRIVER0_PAGE_COUNT         = 2;            // should be power of 2
   // Page size  (bytes)                   
   parameter DRIVER0_PAGE_SIZE          = 4096;  
                 
   // MONITOR0 PARAMETERS
   // Monitor data width
   parameter MONITOR0_DATA_WIDTH         = TXDWIDTH;
   parameter MONITOR0_DREM_WIDTH         = TXDREMWIDTH;
   // Weight of delay enable between transactions           
   parameter MONITOR0_DELAYEN_WT         = 1;  
   // Weight of delay disable between transactions                   
   parameter MONITOR0_DELAYDIS_WT        = 50; 
   // Low boundary delay between transactions                   
   parameter MONITOR0_DELAYLOW           = 0; 
   // High boundary delay between transactions                     
   parameter MONITOR0_DELAYHIGH          = 7; 
   // Weight of delay enable in transaction                    
   parameter MONITOR0_INSIDE_DELAYEN_WT  = 1; 
   // Weight of delay disable in transaction                  
   parameter MONITOR0_INSIDE_DELAYDIS_WT = 50; 
   // Low boundary delay in transaction                  
   parameter MONITOR0_INSIDE_DELAYLOW    = 0; 
   // High boundary delay in transaction                       
   parameter MONITOR0_INSIDE_DELAYHIGH   = 7;                     

   // TEST PARAMETERS
   parameter TRANSACTION_COUNT = 1000; // Count of transactions to generate

endpackage
