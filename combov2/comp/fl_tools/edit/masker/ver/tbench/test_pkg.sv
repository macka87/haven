/*
 * test_pkg.sv: Test package
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobiersky <kobiersky@liberouter.org>
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
 * $Id: test_pkg.sv 15029 2010-08-13 07:02:07Z polcak_l $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package test_pkg;
   
   import math_pkg::*;       // log2()
   
   // Include this file if you want to use standard SystemVerilog Scoreboard
   `include "scoreboard.sv"
   
   // Include this file if you want to use C plus plus Scoreboard
   // `include "dpi/dpi_scoreboard.sv"

   parameter CYCLES = 5;

   // DUT GENERICS
   parameter FL_WIDTH = 128;                             // FrameLink width
   parameter NUMBER_OF_WORDS = 4;                       // number of words in frame
   parameter PARTS = 1;                                 // number of parts
   parameter RX_DATA_WIDTH = FL_WIDTH;                  // 
   parameter RX_DREM_WIDTH = log2(RX_DATA_WIDTH/8);     // 
   parameter TX_DATA_WIDTH = FL_WIDTH;                  // 
   parameter TX_DREM_WIDTH = log2(TX_DATA_WIDTH/8);     // 
   parameter RX_PIPE = 1;                               // pipeline for RX
   parameter TX_PIPE = 1;                               // pipeline for TX
  
   bit[NUMBER_OF_WORDS*FL_WIDTH -1 : 0] RESET_VALUE = '1;

   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TRANSACTION FORMAT (GENERATOR 0)
   // pocet paketov vo frame
   parameter GENERATOR0_FL_PACKET_COUNT      = PARTS;
   // maximalna velkost paketov                
   int       GENERATOR0_FL_PACKET_SIZE_MAX[] = '{FL_WIDTH*NUMBER_OF_WORDS/8}; 
   // minimalna velkost paketov     
   int       GENERATOR0_FL_PACKET_SIZE_MIN[] = '{FL_WIDTH*NUMBER_OF_WORDS/8};         

   // DRIVER0 PARAMETERS
   // datova sirka driveru
   parameter DRIVER0_DATA_WIDTH         = RX_DATA_WIDTH;
   // drem sirka driveru         
   parameter DRIVER0_DREM_WIDTH         = RX_DREM_WIDTH;
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
   // datova sirka monitoru
   parameter MONITOR0_DATA_WIDTH         = TX_DATA_WIDTH; 
   // drem sirka monitoru        
   parameter MONITOR0_DREM_WIDTH         = TX_DREM_WIDTH;
   // vaha delay enable medzi transakciami          
   parameter MONITOR0_DELAYEN_WT         = 1;  
   // vaha delay disable medzi transakciami                   
   parameter MONITOR0_DELAYDIS_WT        = 3; 
   // spodna hranica delay medzi transakciami                    
   parameter MONITOR0_DELAYLOW           = 0; 
   // horna hranica delay medzi transakciami                    
   parameter MONITOR0_DELAYHIGH          = 3; 
   // vaha delay enable v transakcii                     
   parameter MONITOR0_INSIDE_DELAYEN_WT  = 1; 
   // vaha delay disable v transakcii                    
   parameter MONITOR0_INSIDE_DELAYDIS_WT = 3; 
   // spodna hranica delay v transakcii                    
   parameter MONITOR0_INSIDE_DELAYLOW    = 0; 
   // horna hranica delay v transakcii                    
   parameter MONITOR0_INSIDE_DELAYHIGH   = 3;                     


   // TEST PARAMETERS
   parameter TRANSACTION_COUT = 1000; // Count of transactions to generate

endpackage
