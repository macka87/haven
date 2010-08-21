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
 * $Id: test_pkg.sv 9257 2009-07-09 14:16:49Z xsanta06 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package test_pkg;
   
   import math_pkg::*;//log2
   
   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TESTBENCH PARAMETERS
   parameter TXDWIDTH    = 16;
   parameter TXDREMWIDTH = log2(TXDWIDTH/8);
   
   parameter RXDWIDTH    = 16;
   parameter RXDREMWIDTH = log2(RXDWIDTH/8);
   
   parameter IBWIDTH     = 64;
   
   parameter FLOWS       = 4;
   
   // RAM FORMAT
   parameter PAGE_SIZE   = 4096;        // Size of one page
   parameter PAGE_COUNT  = 16;          // Count of pages for each sw buffer
   
   // TRANSACTION FORMAT
   parameter GENERATOR_PACKET_COUNT      = 2;           // Number of packets in one frame
   int       GENERATOR_PACKET_SIZE_MAX[] = '{64,1536};   // Max size of packets
   int       GENERATOR_PACKET_SIZE_MIN[] = '{8,32};      // Min size of packets
   
   // CONTROLLERS PAUSING PARAMETERS
   // Controllers pause enabling
   parameter RX_PAUSE_ALLOWED           = 0;
   parameter TX_PAUSE_ALLOWED           = 0;
   // Pause all RX/TX controllers at the same time 
   // othrewise randomly pause controllers        
   parameter RX_PAUSE_ALL               = 0;         
   parameter TX_PAUSE_ALL               = 0;
   // Between pauses delay                    
   parameter PAUSE_DELAYLOW             = 30000;                   
   parameter PAUSE_DELAYHIGH            = 40000; 
   // Pause time                    
   parameter INSIDE_PAUSE_DELAYLOW      = 10000;                    
   parameter INSIDE_PAUSE_DELAYHIGH     = 25000; 
   
   // CONTROLLERS STOPPING PARAMETERS
   // Controllers stop enabling
   parameter RX_STOP_ALLOWED           = 1;
   parameter TX_STOP_ALLOWED           = 1;
   // Stop all RX/TX controllers at the same time 
   // othrewise randomly stop controllers        
   parameter RX_STOP_ALL               = 0;         
   parameter TX_STOP_ALL               = 0;
   // Between stops delay                    
   parameter STOP_DELAYLOW             = 30000;                   
   parameter STOP_DELAYHIGH            = 140000; 
   // Stop time                    
   parameter INSIDE_STOP_DELAYLOW      = 10000;                    
   parameter INSIDE_STOP_DELAYHIGH     = 125000; 
   
   // DRIVER0 PARAMETERS
   // datova sirka driveru
   parameter DRIVER0_DATA_WIDTH         = RXDWIDTH;
   // drem sirka driveru         
   parameter DRIVER0_DREM_WIDTH         = RXDREMWIDTH;
   // vaha delay enable medzi transakciami         
   parameter DRIVER0_DELAYEN_WT         = 0;
   // vaha delay disable medzi transakciami                     
   parameter DRIVER0_DELAYDIS_WT        = 50;  
   // spodna hranica delay medzi transakciami                   
   parameter DRIVER0_DELAYLOW           = 0; 
   // horna hranica delay medzi transakciami                    
   parameter DRIVER0_DELAYHIGH          = 7; 
   // vaha delay enable v transakcii                    
   parameter DRIVER0_INSIDE_DELAYEN_WT  = 0;
   // vaha delay disable v transakcii                     
   parameter DRIVER0_INSIDE_DELAYDIS_WT = 50;  
   // spodna hranica delay v transakcii                   
   parameter DRIVER0_INSIDE_DELAYLOW    = 0; 
   // horna hranica delay v transakcii                    
   parameter DRIVER0_INSIDE_DELAYHIGH   = 7;      
                  

   // MONITOR0 PARAMETERS
   // datova sirka monitora
   parameter MONITOR0_DATA_WIDTH         = TXDWIDTH;
   // drem sirka driveru 
   parameter MONITOR0_DREM_WIDTH         = TXDREMWIDTH;
   // vaha delay enable medzi transakciami          
   parameter MONITOR0_DELAYEN_WT         = 0;  
   // vaha delay disable medzi transakciami                   
   parameter MONITOR0_DELAYDIS_WT        = 50; 
   // spodna hranica delay medzi transakciami                    
   parameter MONITOR0_DELAYLOW           = 0; 
   // horna hranica delay medzi transakciami                    
   parameter MONITOR0_DELAYHIGH          = 7; 
   // vaha delay enable v transakcii                     
   parameter MONITOR0_INSIDE_DELAYEN_WT  = 0; 
   // vaha delay disable v transakcii                    
   parameter MONITOR0_INSIDE_DELAYDIS_WT = 50; 
   // spodna hranica delay v transakcii                    
   parameter MONITOR0_INSIDE_DELAYLOW    = 0; 
   // horna hranica delay v transakcii                    
   parameter MONITOR0_INSIDE_DELAYHIGH   = 7;                     


   // TEST PARAMETERS
   // Count of transactions to generate in RX direction
   parameter RX_TRANSACTION_COUNT = 250000;
   // Count of transactions to generate in TX direction
   parameter TX_TRANSACTION_COUNT = 1000000;

endpackage
