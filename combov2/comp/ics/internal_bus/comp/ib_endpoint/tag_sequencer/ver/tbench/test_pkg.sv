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
 * $Id: test_pkg.sv 14346 2010-07-13 13:38:11Z xsanta06 $
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
   parameter CLK_PERIOD = 6.4ns;
   parameter RESET_TIME       = 10*CLK_PERIOD;

   // -------- DUT PARAMETERS ------------------------------------------------
   parameter USR_TAG_WIDTH = 5;
   parameter EP_TAG_WIDTH  = 3;

   // -------- TEST PARAMETERS -----------------------------------------------
    // Count of transactions to generate
   parameter TRANSACTION_COUNT = 10000;
    // RNG seed
   parameter RNG_SEED          = 26;

  // -------- TAG DRIVER PARAMETERS ---------------------------------------
    // Delay enable/disable between transactions weight          
   parameter DRIVER_DELAYEN_WT           = 1;  
   parameter DRIVER_DELAYDIS_WT          = 5; 
    // Delay between transactions limits                    
   parameter DRIVER_DELAYLOW             = 3; 
   parameter DRIVER_DELAYHIGH            = 7; 

  // -------- TAG ENDPOINT PARAMETERS -------------------------------------
    // Delay enable/disable between transactions weight          
   parameter EP_DELAYEN_WT              = 1;  
   parameter EP_DELAYDIS_WT             = 5; 
    // Delay between transactions limits                    
   parameter EP_DELAYLOW                = 0; 
   parameter EP_DELAYHIGH               = 7; 
    // Delay enable/disable between transactions weight          
   parameter EP_OP_DELAYEN_WT           = 3;  
   parameter EP_OP_DELAYDIS_WT          = 7; 
    // Delay between transactions limits                    
   parameter EP_OP_DELAYLOW             = 5; 
   parameter EP_OP_DELAYHIGH            = 20; 


endpackage
