/*
 * test_pkg.sv: Test package
 * Copyright (C) 2008 CESNET
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
 * $Id: test_pkg.sv 4023 2008-07-28 07:55:13Z xsimko03 $
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
   // Include this file if you want to use standard SystemVerilog Coverage
   `include "command_coverage.sv"
   
  
   // nastavenie parametrov pre interface, volanie v testbench
   // parametre interface
   parameter DATA_WIDTH      = 64;       // datova sirka 
   parameter FLOWS           = 8;        // pocet vystupnych tokov
   parameter BLOCK_SIZE      = 512;      // max pocet poloziek v bloku   
   parameter LUT_MEMORY      = 0;        // typ pamati pouzity pre ulozenie dat   
   parameter GLOB_STATE      = 0;        // globalny stav                                    
   
   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // doplni sa po dokonceni 

   // TRANSACTION FORMAT (GENERATOR 0)
   // sirka dat
   parameter GENERATOR0_DATA_SIZE      = DATA_WIDTH;
   // pocet vystupnych tokov                
   parameter GENERATOR0_FLOW_COUNT     = FLOWS; 

   // DRIVER0 PARAMETERS
   // datova sirka driveru
   parameter DRIVER0_DATA_WIDTH         = DATA_WIDTH;
   // pocet tokov         
   parameter DRIVER0_FLOWS              = FLOWS;
   // sirka bloku         
   parameter DRIVER0_BLOCK_SIZE         = BLOCK_SIZE;
   // typ pamate (0 = BRAM, 1 = LUT)                    
   parameter DRIVER0_LUT_MEMORY         = LUT_MEMORY;  
   // globalny stav (0 = )                  
   parameter DRIVER0_GLOB_STATE         = GLOB_STATE; 
   // vaha delay enable medzi transakciami
   parameter DRIVER0_DELAYEN_WT         = 1;
   // vaha delay disable medzi transakciami                     
   parameter DRIVER0_DELAYDIS_WT        = 3;  
   // spodna hranica delay medzi transakciami                   
   parameter DRIVER0_DELAYLOW           = 0; 
   // horna hranica delay medzi transakciami                    
   parameter DRIVER0_DELAYHIGH          = 3;                     

   // MONITOR0 PARAMETERS
   // datova sirka monitoru
   parameter MONITOR0_DATA_WIDTH        = DATA_WIDTH; 
   // pocet tokov
   parameter MONITOR0_FLOWS             = FLOWS;
   // sirka bloku         
   parameter MONITOR0_BLOCK_SIZE        = BLOCK_SIZE;
   // typ pamate (0 = BRAM, 1 = LUT)                    
   parameter MONITOR0_LUT_MEMORY        = LUT_MEMORY;  
   // globalny stav (0 = )                  
   parameter MONITOR0_GLOB_STATE        = GLOB_STATE; 
   // vaha delay enable medzi transakciami
   parameter MONITOR0_DELAYEN_WT        = 1;
   // vaha delay disable medzi transakciami                     
   parameter MONITOR0_DELAYDIS_WT       = 3;  
   // spodna hranica delay medzi transakciami                   
   parameter MONITOR0_DELAYLOW          = 0; 
   // horna hranica delay medzi transakciami                    
   parameter MONITOR0_DELAYHIGH         = 10;                           


   // TEST PARAMETERS
   parameter TRANSACTION_COUNT =3000; // Count of transactions to generate
   
endpackage
