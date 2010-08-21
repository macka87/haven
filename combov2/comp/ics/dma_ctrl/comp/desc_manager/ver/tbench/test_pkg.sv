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
 * $Id: test_pkg.sv 5194 2008-08-25 07:46:47Z xsimko03 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package test_pkg;
   
   // set parameters for interface, they are calling in testbench
   // parametres of interface

   parameter BASE_ADDR       = 32'h02200000;    // Base Address

   parameter INIT_OFFSET     = BASE_ADDR+(20'h40000);    

   parameter FLOWS           = 8;              // Number of Flows           
   parameter BLOCK_SIZE      = 64;              // Block Size of Item space for one Flow      

    
   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;
 
   // TRANSACTION FORMAT (GENERATOR 0)
   // Data Size
   parameter GENERATOR0_DATA_SIZE      = 64;
   // Number of Output Flows                
   parameter GENERATOR0_FLOW_COUNT     = FLOWS;  

   // DRIVER0 PARAMETERS
   // Base Address
   parameter DRIVER0_BASE_ADDR          = BASE_ADDR;         
   // Number of Input Flows        
   parameter DRIVER0_FLOWS              = FLOWS;
   // Block Size         
   parameter DRIVER0_BLOCK_SIZE         = BLOCK_SIZE;
   // range of descriptors in one flow
   parameter DRIVER0_RANGE              = 8192;
   
                      
   // delay enable between transactions
   parameter DRIVER0_DELAYEN_WT         = 1;
   // delay disable between transactions                     
   parameter DRIVER0_DELAYDIS_WT        = 3;  
   // low boundary delay between transactions                   
   parameter DRIVER0_DELAYLOW           = 0; 
   // high boundary delay between transactions                   
   parameter DRIVER0_DELAYHIGH          = 3;                     
 
 
   // MONITOR0 PARAMETERS
   // datova sirka monitoru
   parameter MONITOR0_BASE_ADDR         = BASE_ADDR;
   // pocet tokov
   parameter MONITOR0_FLOWS             = FLOWS;
   // sirka bloku         
   parameter MONITOR0_BLOCK_SIZE        = BLOCK_SIZE;
                         
   // vaha delay enable medzi transakciami
   parameter MONITOR0_DELAYEN_WT        = 1;
   // vaha delay disable medzi transakciami                     
   parameter MONITOR0_DELAYDIS_WT       = 3;  
   // spodna hranica delay medzi transakciami                   
   parameter MONITOR0_DELAYLOW          = 0; 
   // horna hranica delay medzi transakciami                    
   parameter MONITOR0_DELAYHIGH         = 10;   
   
   // TEST PARAMETERS

   parameter TRANSACTION_COUNT =1000; // Count of transactions to generate
     
endpackage
