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
 * $Id: test_pkg.sv 14773 2010-08-03 12:17:38Z xsanta06 $
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
   parameter XGMII_CLK_PERIOD = 6.4ns;
   parameter FL_CLK_PERIOD    = 10ns;
   parameter MI32_CLK_PERIOD  = 10ns;
   parameter RESET_TIME       = 10*FL_CLK_PERIOD;

   // -------- DUT PARAMETERS ------------------------------------------------
    // Number of items in Data FIFO (FL_WIDTH_TX + control signals wide).
    // !!!!!!!!!!! Must be 2^n, n>=2 !!!!!!!!!!!!!!!!!!!!!!
   parameter DFIFO_SIZE     = 4096;
    // HFIFO item count (1-bit wide)
   parameter HFIFO_SIZE     = 1024;
    // Type of the memory used in HFIFO
   parameter HFIFO_MEMTYPE  = 0;
    // Frames contain control part
   parameter CTRL_CMD       = 0;
    // FrameLink width
   parameter FL_WIDTH_RX    = 128;

   // TESTBENCH PARAMETERS
   parameter FL_REM_WIDTH_RX = log2(FL_WIDTH_RX/8);
   
   // -------- TEST PARAMETERS -----------------------------------------------
    // Count of transactions to generate
   parameter TRANSACTION_COUNT = 50000;

   // -------- OBUF CONFIGURATION --------------------------------------------
    // MAC address
//   parameter logic[47:0] MAC_ADDRESS = 48'hAABBCCDDEEFF;
   parameter logic[47:0] MAC_ADDRESS = 48'hFFEEDDCCBBAA;

   // -------- FL TRANSACTION FORMAT --------------------------------------
    // FL packet size
   parameter FL_PART_COUNT          = 1 + CTRL_CMD;
   int       FL_PART_SIZE_MAX[]     = '{1526, 4};
   int       FL_PART_SIZE_MIN[]     = '{32, 1};
    // FrameLink footer bit 0 (discard frame) set to 0 weight
   parameter FL_DISCARD_ZERO_WT      = 1;
    // FrameLink footer bit 0 (discard frame) set to 1 weight
   parameter FL_DISCARD_ONE_WT       = 10;
    // FrameLink footer bit 0 (replace MAC address) set to 0 weight
   parameter FL_REPLACEMAC_ZERO_WT   = 1;
    // FrameLink footer bit 0 (replace MAC address) set to 1 weight
   parameter FL_REPLACEMAC_ONE_WT    = 10;


   // -------- FL DRIVER PARAMETERS -----------------------------------------
    // FL data width
   parameter DRIVER0_DATA_WIDTH         = FL_WIDTH_RX;
    // FL REM width 
   parameter DRIVER0_DREM_WIDTH         = FL_REM_WIDTH_RX;
    // Delay enable/disable between transactions weight          
   parameter DRIVER0_DELAYEN_WT         = 0;  
   parameter DRIVER0_DELAYDIS_WT        = 5; 
    // Delay between transactions limits                    
   parameter DRIVER0_DELAYLOW           = 0; 
   parameter DRIVER0_DELAYHIGH          = 7; 
    // Delay enable/disalbe inside transaction weight          
   parameter DRIVER0_INSIDE_DELAYEN_WT  = 0; 
   parameter DRIVER0_INSIDE_DELAYDIS_WT = 5; 
    // Delay inside transaction limits                    
   parameter DRIVER0_INSIDE_DELAYLOW    = 0; 
   parameter DRIVER0_INSIDE_DELAYHIGH   = 7;                     

endpackage
