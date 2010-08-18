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
 * $Id: test_pkg.sv 10112 2009-08-05 20:53:51Z polcak_l $
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
  
   // DUT GENERICS
   
   parameter INPUT_WIDTH = 16;          // 16,128      
   parameter OUTPUT_WIDTH = 64;         // 16,32,64,128      
   parameter INPUT_COUNT = 3;           // 1,2,4,8      
   parameter PARTS = 3;                 // present of header, footer        
   parameter TICKET_PART = 1;           // ticket is in first part of frame 1  
   parameter TICKET_OFFSET = 2;         // Offset of the ticket 0,2
   parameter TICKET_SIZE = 2;           // Size of the ticket 2     
   parameter TICKET_FIFO_ITEMS = 128;           
   parameter INPUT_FIFO_ITEMS = 1024;                  
   parameter OUTPUT_FIFO_ITEMS = 128; 
     
   parameter INPUT_DREM_WIDTH = log2(INPUT_WIDTH/8);    
   parameter OUTPUT_DREM_WIDTH = log2(OUTPUT_WIDTH/8);   
     
   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TRANSACTION FORMAT
   parameter GENERATOR_FL_PACKET_COUNT      = PARTS;            // pocet paketov vo frame
   int       GENERATOR_FL_PACKET_SIZE_MAX[] = '{64,1536,64};    // maximalna velkost paketov
   int       GENERATOR_FL_PACKET_SIZE_MIN[] = '{32,64,32};        // minimalna velkost paketov

   // DRIVER0 PARAMETERS
   parameter DRIVER_DATA_WIDTH         = INPUT_WIDTH;        // datova sirka driveru
   parameter DRIVER_DREM_WIDTH         = INPUT_DREM_WIDTH;   // drem sirka driveru
   parameter DRIVER_DELAYEN_WT         = 1;                  // vaha delay enable medzi transakciami
   parameter DRIVER_DELAYDIS_WT        = 50;                 // vaha delay disable medzi transakciami
   parameter DRIVER_DELAYLOW           = 0;                  // spodna hranica delay medzi transakciami
   parameter DRIVER_DELAYHIGH          = 10;                 // horna hranica delay medzi transakciami
   parameter DRIVER_INSIDE_DELAYEN_WT  = 1;                  // vaha delay enable v transakcii
   parameter DRIVER_INSIDE_DELAYDIS_WT = 50;                 // vaha delay disable v transakcii
   parameter DRIVER_INSIDE_DELAYLOW    = 0;                  // spodna hranica delay v transakcii
   parameter DRIVER_INSIDE_DELAYHIGH   = 10;                 // horna hranica delay v transakcii
   
   // MONITOR PARAMETERS
   parameter MONITOR_DATA_WIDTH         = OUTPUT_WIDTH;      // datova sirka monitoru
   parameter MONITOR_DREM_WIDTH         = OUTPUT_DREM_WIDTH; // drem sirka monitoru
   parameter MONITOR_DELAYEN_WT         = 1;                 // vaha delay enable medzi transakciami 
   parameter MONITOR_DELAYDIS_WT        = 50;                // vaha delay disable medzi transakciami
   parameter MONITOR_DELAYLOW           = 0;                 // spodna hranica delay medzi transakciami
   parameter MONITOR_DELAYHIGH          = 10;                // horna hranica delay medzi transakciami
   parameter MONITOR_INSIDE_DELAYEN_WT  = 1;                 // vaha delay enable v transakcii 
   parameter MONITOR_INSIDE_DELAYDIS_WT = 50;                // vaha delay disable v transakcii
   parameter MONITOR_INSIDE_DELAYLOW    = 0;                 // spodna hranica delay v transakcii
   parameter MONITOR_INSIDE_DELAYHIGH   = 10;                // horna hranica delay v transakcii


   // TEST PARAMETERS
   parameter TRANSACTION_COUNT = 20000; // Count of transactions to generate

endpackage
