/*
 * test_pkg.sv: Test package
 * Copyright (C) 2010 CESNET
 * Author(s): Marek Santa <santa@liberouter.org>
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
 * $Id: test_pkg.sv 15016 2010-08-12 12:32:34Z xsanta06 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package test_pkg;
   
   import math_pkg::*;//log2, max
   
   // -- CLOCKS AND RESETS ---------------------------------------------------
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // -- DUT PARAMETERS ------------------------------------------------------
    // Number of network interfaces
   parameter RX_IFC_COUNT              = 4;    // T Change also in
   parameter TX_IFC_COUNT              = 2;    // |
   parameter RX_BUFFER_SIZE            = 4096; // |
   parameter TX_BUFFER_SIZE            = 4096; // |
   parameter RX_FL_WIDTH               = 64;   // |
   parameter TX_FL_WIDTH               = 64;   // L -> ../ver_const.vhd
   
    // Buffers block size
   parameter RX_BLOCK_SIZE             = (RX_BUFFER_SIZE/(RX_FL_WIDTH/8));
    // Generic allowing generation of FL_DISCARD_STAT entity before RX Buffer
   parameter RX_DISCARD_EN             = 1;
    // Descriptor manager generics
   parameter DESC_BASE_ADDR            = 32'h02200000;
   parameter DESC_BLOCK_SIZE           = 4;

   // -- TESTBENCH PARAMETERS ------------------------------------------------
   parameter TXDWIDTH    = 64; //16;
   parameter TXDREMWIDTH = log2(TXDWIDTH/8);
   
   parameter RXDWIDTH    = 64; //16;
   parameter RXDREMWIDTH = log2(RXDWIDTH/8);
   
   parameter IBWIDTH     = 64;
   
   parameter FLOWS       = max(RX_IFC_COUNT, TX_IFC_COUNT);

   parameter STATUSWIDTH = log2(RX_BLOCK_SIZE+1);
   
   // -- RAM FORMAT ----------------------------------------------------------
   parameter PAGE_SIZE   = 4096;        // Size of one page
   parameter PAGE_COUNT  = 16;          // Count of pages for each sw buffer
   
   // -- TRANSACTION FORMAT --------------------------------------------------
   parameter GENERATOR_PACKET_COUNT      = 2;           // Number of packets in one frame
   int       GENERATOR_PACKET_SIZE_MAX[] = '{64,1536};   // Max size of packets
   int       GENERATOR_PACKET_SIZE_MIN[] = '{8,32};      // Min size of packets
   
   // CONTROLLERS PAUSING PARAMETERS
   // Controllers pause enabling
   parameter RX_PAUSE_ALLOWED           = 0;
   parameter TX_PAUSE_ALLOWED           = 0;
   // Pause all RX/TX controllers at the same time 
   // othrewise randomly pause controllers        
   parameter RX_PAUSE_ALL               = 1;         
   parameter TX_PAUSE_ALL               = 1;
   // Between pauses delay                    
   parameter PAUSE_DELAYLOW             = 30000;                   
   parameter PAUSE_DELAYHIGH            = 40000; 
   // Pause time                    
   parameter INSIDE_PAUSE_DELAYLOW      = 10000;                    
   parameter INSIDE_PAUSE_DELAYHIGH     = 25000; 
   
   // CONTROLLERS STOPPING PARAMETERS
   // Controllers stop enabling
   parameter RX_STOP_ALLOWED           = 1;
   parameter TX_STOP_ALLOWED           = 0;
   // Stop all RX/TX controllers at the same time 
   // othrewise randomly stop controllers        
   parameter RX_STOP_ALL               = 1;         
   parameter TX_STOP_ALL               = 1;
   // Between stops delay                    
   parameter STOP_DELAYLOW             = 30000;                   
   parameter STOP_DELAYHIGH            = 40000; 
   // Stop time                    
   parameter INSIDE_STOP_DELAYLOW      = 10000;                    
   parameter INSIDE_STOP_DELAYHIGH     = 25000; 
   
   // -- DRIVER PARAMETERS ---------------------------------------------------
    // FL data width
   parameter DRIVER0_DATA_WIDTH         = RXDWIDTH;
    // FL REM width 
   parameter DRIVER0_DREM_WIDTH         = RXDREMWIDTH;
    // Delay enable/disable between transactions weight          
   parameter DRIVER0_DELAYEN_WT         = 0;
   parameter DRIVER0_DELAYDIS_WT        = 50;  
    // Delay between transactions limits                    
   parameter DRIVER0_DELAYLOW           = 0; 
   parameter DRIVER0_DELAYHIGH          = 7; 
    // Delay enable/disalbe inside transaction weight          
   parameter DRIVER0_INSIDE_DELAYEN_WT  = 0;
   parameter DRIVER0_INSIDE_DELAYDIS_WT = 50;  
    // Delay inside transaction limits                    
   parameter DRIVER0_INSIDE_DELAYLOW    = 0; 
   parameter DRIVER0_INSIDE_DELAYHIGH   = 7;      
                  

   // -- MONITOR PARAMETERS --------------------------------------------------
    // FL data width
   parameter MONITOR0_DATA_WIDTH         = TXDWIDTH;
    // FL REM width 
   parameter MONITOR0_DREM_WIDTH         = TXDREMWIDTH;
    // Delay enable/disable between transactions weight          
   parameter MONITOR0_DELAYEN_WT         = 0;  
   parameter MONITOR0_DELAYDIS_WT        = 50; 
    // Delay between transactions limits                    
   parameter MONITOR0_DELAYLOW           = 0; 
   parameter MONITOR0_DELAYHIGH          = 7; 
    // Delay enable/disalbe inside transaction weight          
   parameter MONITOR0_INSIDE_DELAYEN_WT  = 0; 
   parameter MONITOR0_INSIDE_DELAYDIS_WT = 50; 
    // Delay inside transaction limits                    
   parameter MONITOR0_INSIDE_DELAYLOW    = 0; 
   parameter MONITOR0_INSIDE_DELAYHIGH   = 7;                     

   // -- MULTIPLEXOR PARAMETERS ----------------------------------------------
    // Delay between multiplexing limits                    
   parameter MULTIPLEXOR_MUXDELAYLOW     = 2; 
   parameter MULTIPLEXOR_MUXDELAYHIGH    = 12; 

   // -- TEST PARAMETERS -----------------------------------------------------
   // Count of transactions to generate in RX direction
   parameter RX_TRANSACTION_COUNT = 5000;
   // Count of transactions to generate in TX direction
   parameter TX_TRANSACTION_COUNT = 1;

endpackage
