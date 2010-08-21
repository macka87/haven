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
 * $Id: test_pkg.sv 11763 2009-10-26 21:53:09Z xvikto03 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
// FrameLink MARKER Mark Interface
`include "fl_simple_marker_ifc.sv"

package test_pkg;
   
   import math_pkg::*;       // log2()
   
   // Include Scoreboard and Mark_generator
   `include "scoreboard.sv"
   `include "fl_simple_marker_mark_generator.sv"
   
   // DUT GENERICS
   parameter DATA_WIDTH   =   128;        // Data width
   parameter PARTS        =   2;         // Number of FL parts
   parameter MARK_PART    =   0;         // Which part will be marked 
   parameter OFFSET       =   24;         // Mark position in FL packet in Bytes (Count from 0)
   parameter MARK_SIZE    =   16;         // Size of MARK in Bytes 
   parameter INSERT       =   0;         // Switch between insert and rewrite mode

   // TEST PARAMETERS
   parameter TRANSACTION_COUNT =   3000; // Count of transactions to generate
   
   parameter DREM_WIDTH   = log2(DATA_WIDTH/8);     // Data Reminder width

   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TRANSACTION FORMAT (GENERATOR 0)
   // pocet paketov vo frame
   parameter GENERATOR0_FL_PACKET_COUNT      = PARTS;
   // maximalna velkost paketov                
   int       GENERATOR0_FL_PACKET_SIZE_MAX[] = '{32, 1536, 32}; 
   // minimalna velkost paketov     
   int       GENERATOR0_FL_PACKET_SIZE_MIN[] = '{1, 64, 1};         

   // DRIVER0 PARAMETERS
   // datova sirka driveru
   parameter DRIVER0_DATA_WIDTH         = DATA_WIDTH;
   // drem sirka driveru         
   parameter DRIVER0_DREM_WIDTH         = DREM_WIDTH;
   // vaha delay enable medzi transakciami         
   parameter DRIVER0_DELAYEN_WT         = 1;
   // vaha delay disable medzi transakciami                     
   parameter DRIVER0_DELAYDIS_WT        = 50;  
   // spodna hranica delay medzi transakciami                   
   parameter DRIVER0_DELAYLOW           = 0; 
   // horna hranica delay medzi transakciami                    
   parameter DRIVER0_DELAYHIGH          = 10; 
   // vaha delay enable v transakcii                    
   parameter DRIVER0_INSIDE_DELAYEN_WT  = 1;
   // vaha delay disable v transakcii                     
   parameter DRIVER0_INSIDE_DELAYDIS_WT = 50;  
   // spodna hranica delay v transakcii                   
   parameter DRIVER0_INSIDE_DELAYLOW    = 0; 
   // horna hranica delay v transakcii                    
   parameter DRIVER0_INSIDE_DELAYHIGH   = 10;                     

   // MONITOR0 PARAMETERS
   // datova sirka monitoru
   parameter MONITOR0_DATA_WIDTH         = DATA_WIDTH; 
   // drem sirka monitoru        
   parameter MONITOR0_DREM_WIDTH         = DREM_WIDTH;
   // vaha delay enable medzi transakciami          
   parameter MONITOR0_DELAYEN_WT         = 1;  
   // vaha delay disable medzi transakciami                   
   parameter MONITOR0_DELAYDIS_WT        = 50; 
   // spodna hranica delay medzi transakciami                    
   parameter MONITOR0_DELAYLOW           = 0; 
   // horna hranica delay medzi transakciami                    
   parameter MONITOR0_DELAYHIGH          = 10; 
   // vaha delay enable v transakcii                     
   parameter MONITOR0_INSIDE_DELAYEN_WT  = 1; 
   // vaha delay disable v transakcii                    
   parameter MONITOR0_INSIDE_DELAYDIS_WT = 50; 
   // spodna hranica delay v transakcii                    
   parameter MONITOR0_INSIDE_DELAYLOW    = 0; 
   // horna hranica delay v transakcii                    
   parameter MONITOR0_INSIDE_DELAYHIGH   = 10;                     

   // MARK GENERATOR PARAMETERS
   // vaha delay enable medzi transakciami          
   parameter MARK_DELAYEN_WT         = 1;  
   // vaha delay disable medzi transakciami                   
   parameter MARK_DELAYDIS_WT        = 5; 
   // spodna hranica delay medzi transakciami                    
   parameter MARK_DELAYLOW           = 0; 
   // horna hranica delay medzi transakciami                    
   parameter MARK_DELAYHIGH          = 10; 

endpackage
