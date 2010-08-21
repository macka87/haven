/*
 * test_pkg.sv: Test package
 * Copyright (C) 2009 CESNET
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
 * $Id: test_pkg.sv 11940 2009-11-09 18:22:03Z xvikto03 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package test_pkg;

   import math_pkg::*; // log2()

   // Write debugging information
   `define DEBUG

   // Include Scoreboard
   `include "scoreboard.sv"
  
   // DUT GENERICS
   parameter DATA_WIDTH    =  128;   // Input/output data width
   parameter OUTPUT_COUNT  =  8;    // Number of output interfaces
   parameter DEFAULT_IFC   =  1;    // Default interface when mark is missing
   parameter INUM_OFFSET   =  64;  // Mark offset from begin of PART_NUM part
                                   //   in bits. Mark cannot be between two
                                   //   words.
   parameter PARTS         =  1;
   
   // TEST PARAMETERS
   parameter TRANSACTION_COUT = 200; // Count of transactions to generate

 
   // TESTBENCH PARAMETERS
   parameter DREM_WIDTH  = log2(DATA_WIDTH/8);            
   parameter FRAME_PARTS =  1;
      
   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TRANSACTION FORMAT
   parameter GENERATOR_FL_PACKET_COUNT      = FRAME_PARTS;   // pocet paketov vo frame
   int       GENERATOR_FL_PACKET_SIZE_MAX[] = '{10,15,32};   // maximalna velkost paketov
   int       GENERATOR_FL_PACKET_SIZE_MIN[] = '{4,6,1};      // minimalna velkost paketov

   // DRIVER0 PARAMETERS
   parameter DRIVER_DATA_WIDTH         = DATA_WIDTH;      // datova sirka driveru
   parameter DRIVER_DREM_WIDTH         = DREM_WIDTH;      // drem sirka driveru
   parameter DRIVER_DELAYEN_WT         = 1;                  // vaha delay enable medzi transakciami
   parameter DRIVER_DELAYDIS_WT        = 50;                  // vaha delay disable medzi transakciami
   parameter DRIVER_DELAYLOW           = 0;                  // spodna hranica delay medzi transakciami
   parameter DRIVER_DELAYHIGH          = 10;                  // horna hranica delay medzi transakciami
   parameter DRIVER_INSIDE_DELAYEN_WT  = 1;                  // vaha delay enable v transakcii
   parameter DRIVER_INSIDE_DELAYDIS_WT = 50;                  // vaha delay disable v transakcii
   parameter DRIVER_INSIDE_DELAYLOW    = 0;                  // spodna hranica delay v transakcii
   parameter DRIVER_INSIDE_DELAYHIGH   = 10;                  // horna hranica delay v transakcii
   
   // MONITOR PARAMETERS
   parameter MONITOR_DATA_WIDTH         = DATA_WIDTH;     // datova sirka monitoru
   parameter MONITOR_DREM_WIDTH         = DREM_WIDTH;     // drem sirka monitoru
   parameter MONITOR_DELAYEN_WT         = 1;                 // vaha delay enable medzi transakciami 
   parameter MONITOR_DELAYDIS_WT        = 50;                 // vaha delay disable medzi transakciami
   parameter MONITOR_DELAYLOW           = 0;                 // spodna hranica delay medzi transakciami
   parameter MONITOR_DELAYHIGH          = 10;                 // horna hranica delay medzi transakciami
   parameter MONITOR_INSIDE_DELAYEN_WT  = 1;                 // vaha delay enable v transakcii 
   parameter MONITOR_INSIDE_DELAYDIS_WT = 50;                 // vaha delay disable v transakcii
   parameter MONITOR_INSIDE_DELAYLOW    = 0;                 // spodna hranica delay v transakcii
   parameter MONITOR_INSIDE_DELAYHIGH   = 10;                 // horna hranica delay v transakcii


endpackage
