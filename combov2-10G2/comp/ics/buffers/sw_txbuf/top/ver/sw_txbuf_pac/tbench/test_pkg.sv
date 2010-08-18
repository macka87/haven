/*
 * test_pkg.sv: Test package
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
 * $Id: test_pkg.sv 8683 2009-06-05 18:26:37Z xsimko03 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package test_pkg;
   
   import math_pkg::*;       // log2()
   
   // DUT GENERICS
   parameter DATA_WIDTH       = 64;           // Data width
   parameter BLOCK_SIZE       = 512;          // Number of items (DATA_WIDTH width) that can be stored for each flow
   parameter FLOWS            = 1;            // Number of flows (interfaces) 1,2,4
   parameter TOTAL_FLOW_SIZE  = 16384;        // Total size (bytes) for one flow
   
   parameter TX_DATA_WIDTH    = DATA_WIDTH/FLOWS;
   
   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TRANSACTION FORMAT (GENERATOR 0)
   // packets number in frame
   parameter GENERATOR0_FLOWS                = FLOWS;
   parameter GENERATOR0_FL_PACKET_COUNT      = 1;
   // max size of packet                
   int       GENERATOR0_FL_PACKET_SIZE_MAX[] = '{1516};  
   // min size of packet  
   int       GENERATOR0_FL_PACKET_SIZE_MIN[] = '{64}; 

   // SCOREBOARD0 PARAMETERS
   parameter SCOREBOARD0_FLOWS          = FLOWS;
   parameter SCOREBOARD0_BEHAV          = 1;
   
   // DRIVER0 PARAMETERS
   // data_width for driver
   parameter DRIVER0_DATA_WIDTH         = DATA_WIDTH;
   // number of flows        
   parameter DRIVER0_FLOWS              = FLOWS;
   // block size         
   parameter DRIVER0_BLOCK_SIZE         = BLOCK_SIZE;
   // total flow size                   
   parameter DRIVER0_TOTAL_FLOW_SIZE    = TOTAL_FLOW_SIZE;  
   // delay enable between transactions
   parameter DRIVER0_DELAYEN_WT         = 1;
   // delay disable between transactions                     
   parameter DRIVER0_DELAYDIS_WT        = 3;  
   // low bound delay between transactions                   
   parameter DRIVER0_DELAYLOW           = 0; 
   // high bound delay between transactions                    
   parameter DRIVER0_DELAYHIGH          = 3;                     
 
  
   // MONITOR0 PARAMETERS
   // data_width for monitor
   parameter MONITOR0_DATA_WIDTH        = TX_DATA_WIDTH; 
   // number of flows
   parameter MONITOR0_FLOWS             = FLOWS;
   // block size         
   parameter MONITOR0_BLOCK_SIZE        = BLOCK_SIZE;
   // total flow size                      
   parameter MONITOR0_TOTAL_FLOW_SIZE   = TOTAL_FLOW_SIZE;
   // delay enable between transactions         
   parameter MONITOR0_DELAYEN_WT         = 1;  
   // delay disable between transactions                   
   parameter MONITOR0_DELAYDIS_WT        = 3; 
   // low bound delay between transactions                    
   parameter MONITOR0_DELAYLOW           = 0; 
   // horna hranica delay medzi transakciami                    
   parameter MONITOR0_DELAYHIGH          = 3; 
   // delay enable in transaction                     
   parameter MONITOR0_INSIDE_DELAYEN_WT  = 1; 
   // delay disable in transaction                     
   parameter MONITOR0_INSIDE_DELAYDIS_WT = 3; 
   // low bound delay in transaction                   
   parameter MONITOR0_INSIDE_DELAYLOW    = 0; 
   // high bound delay in transaction                    
   parameter MONITOR0_INSIDE_DELAYHIGH   = 3;                          


   // TEST PARAMETERS
   parameter TRANSACTION_COUNT = 5000; // Count of transactions to generate
   
endpackage
