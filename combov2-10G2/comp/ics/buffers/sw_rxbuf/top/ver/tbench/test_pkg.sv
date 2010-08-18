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
 * $Id: test_pkg.sv 3880 2008-07-23 09:01:04Z xsanta06 $
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
   parameter BLOCK_SIZE       = 64;          // Number of items (DATA_WIDTH width) that can be stored for each flow
   parameter FLOWS            = 4;            // Number of flows (interfaces)
   parameter TOTAL_FLOW_SIZE  = 65536;        // Total size (bytes) for one flow
   
   parameter RX_DATA_WIDTH    = DATA_WIDTH/FLOWS;
   
   // DUT CONNECTION PARAMETERS
   parameter REM_WIDTH  = log2((RX_DATA_WIDTH)/8);
   
   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TRANSACTION FORMAT
   parameter GENERATOR_PACKET_COUNT      = 2;           // pocet paketov vo frame
   int       GENERATOR_PACKET_SIZE_MAX[] = '{32,128};   // maximalna velkost paketov
   int       GENERATOR_PACKET_SIZE_MIN[] = '{1,8};      // minimalna velkost paketov
   
   // DRIVER0 PARAMETERS
   // datova sirka driveru
   parameter DRIVER0_DATA_WIDTH         = RX_DATA_WIDTH;
   // vaha delay enable medzi transakciami         
   parameter DRIVER0_DELAYEN_WT         = 1;
   // vaha delay disable medzi transakciami                     
   parameter DRIVER0_DELAYDIS_WT        = 0;  
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
   // datova sirka monitora
   parameter MONITOR0_DATA_WIDTH         = DATA_WIDTH;
   // vaha request delay enable medzi transakciami          
   parameter MONITOR0_REQDELAYEN_WT      = 1;  
   // vaha request delay disable medzi transakciami                   
   parameter MONITOR0_REQDELAYDIS_WT     = 0; 
   // spodna request hranica delay medzi transakciami                    
   parameter MONITOR0_REQDELAYLOW        = 50; 
   // horna request hranica delay medzi transakciami                    
   parameter MONITOR0_REQDELAYHIGH       = 100; 
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
   parameter TRANSACTION_COUNT = 100; // Count of transactions to generate

endpackage
