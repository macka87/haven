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
 * $Id: test_pkg.sv 15127 2010-08-17 07:21:55Z xsanta06 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package test_pkg;

   import math_pkg::*; // log2

   // -- DUT GENERICS --
    // FrameLink data width
   parameter DATA_WIDTH     = 64;
    // Number of channels, up to 64
   parameter CHANNELS       = 4;
    // Width of the STATUS signal for each flow, up to 16 bits
   parameter STATUS_WIDTH   = 10;
    // Width of counters, 16 to 64 bits
   parameter CNT_WIDTH      = 64;
    // Enable various counters
   parameter COUNT_DROP     = 1;
   parameter COUNT_PASS     = 1;
   parameter COUNT_DROP_LEN = 1;
   parameter COUNT_PASS_LEN = 1;
    // Generate output register on output FrameLink
    // (It's possible because on output FrameLink is not used st_rdy_n signal)
   parameter OUTPUT_REG     = 1;

   // -- TESTBENCH PARAMS --
   parameter DREM_WIDTH = log2(DATA_WIDTH/8); // drem width
   
   // -- CLOCKS AND RESETS --
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // -- TRANSACTION FORMAT --
   parameter GENERATOR0_FL_PACKET_COUNT      = 2;
   int       GENERATOR0_FL_PACKET_SIZE_MAX[] = '{64, 1526};
   int       GENERATOR0_FL_PACKET_SIZE_MIN[] = '{8, 64};

   // -- DRIVER0 PARAMETERS --
    // FL data width
   parameter DRIVER0_DATA_WIDTH         = DATA_WIDTH;
    // FL REM width 
   parameter DRIVER0_DREM_WIDTH         = DREM_WIDTH;
    // Delay enable/disable between transactions weight          
   parameter DRIVER0_DELAYEN_WT         = 0;
   parameter DRIVER0_DELAYDIS_WT        = 5;
    // Delay between transactions limits                    
   parameter DRIVER0_DELAYLOW           = 0;
   parameter DRIVER0_DELAYHIGH          = 10;
    // Delay enable/disalbe inside transaction weight          
   parameter DRIVER0_INSIDE_DELAYEN_WT  = 0;
   parameter DRIVER0_INSIDE_DELAYDIS_WT = 5;
    // Delay inside transaction limits                    
   parameter DRIVER0_INSIDE_DELAYLOW    = 0;
   parameter DRIVER0_INSIDE_DELAYHIGH   = 10;

   // -- MONITOR0 PARAMETERS --
    // FL data width
   parameter MONITOR0_DATA_WIDTH         = DATA_WIDTH;
    // FL REM width 
   parameter MONITOR0_DREM_WIDTH         = DREM_WIDTH;

   // -- MULTIPLEXOR PARAMETERS -- 
    // Delay between multiplexing limits                    
   parameter MULTIPLEXOR_MUXDELAYLOW     = 1;
   parameter MULTIPLEXOR_MUXDELAYHIGH    = 3;


   // -- TEST PARAMETERS --
    // Count of transactions to generate
   parameter TRANSACTION_COUNT = 2000;
    // Seed for RNG
   parameter RNG_SEED          = 7;

endpackage
