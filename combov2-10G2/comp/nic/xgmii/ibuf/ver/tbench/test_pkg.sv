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
 * $Id: test_pkg.sv 14738 2010-07-30 13:24:51Z polcak_l $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package test_pkg;
   
   import math_pkg::*;//log2
   
   `define SHOW_XGMII_ERROR 
   `define SHOW_CRC_ERROR 

   // CLOCKS AND RESETS
   parameter XGMII_CLK_PERIOD = 6.4ns;
   parameter FL_CLK_PERIOD    = 10ns;
   parameter MI32_CLK_PERIOD  = 10ns;
   parameter RESET_TIME       = 10*FL_CLK_PERIOD;

   // -------- DUT PARAMETERS ------------------------------------------------
    // Number of items in Data FIFO (FL_WIDTH_TX + control signals wide).
    // !!!!!!!!!!! Must be 2^n, n>=2 !!!!!!!!!!!!!!!!!!!!!!
   parameter DFIFO_SIZE     = 4096;
    // Number of items in Header and Footer FIFO
    // (FL_WIDTH_TX + control signals wide)
   parameter HFIFO_SIZE     = 1024;
    // Type of the memory used in HFIFO
   parameter HFIFO_MEMTYPE  = 1;
    // Enables frame headers
   parameter CTRL_HDR_EN    = 1;
    // Enables frame footers
   parameter CTRL_FTR_EN    = 0;
    // Number of supported MAC addresses (up to 16)
   parameter MACS           = 16;
    // Remove FCS from the packet (false -> remove, true -> don't remove)
   parameter INBANDFCS      = 0;
    // Determines the length of the counter which guards the link for errors
    // If error dont occur for 2^CNT_ERROR_SIZE cycles the link is declared to
    // be up
   parameter CNT_ERROR_SIZE = 5;
    // FrameLink output width (at least 64)
   parameter FL_WIDTH_TX    = 128;
    // Put FL Relay to the output
   parameter FL_RELAY       = 0;

   // TESTBENCH PARAMETERS
   parameter FL_REM_WIDTH_TX = log2(FL_WIDTH_TX/8);
   
   // -------- TEST PARAMETERS -----------------------------------------------
    // Count of transactions to generate
   parameter TRANSACTION_COUNT = 50000;
    // Behavior of XGMII transaction table
    // If set to 1 only the top transaction in FIFO will be compared. Is is
    // usefull for checking correct IBUF discarding due to packet errors (such
    // as CRC error, XGMII error, MTU error, ...) and it needs low delays on
    // FL interface.
    // If set to 0 transactions in FIFO are compared until match and then they
    // are discarded. It is usefull for checking correct IBUF discarding due
    // to buffer overflow, but it doesn't discover packet errors. It needs
    // higher delays on FL interface.
   parameter XGMII_FIRST_ONLY  = 1;

   // -------- IBUF CONFIGURATION --------------------------------------------
    // Set Error Mask Register
   parameter ERR_MASK_REG_XGMII = 1;
   parameter ERR_MASK_REG_CRC   = 1;
   parameter ERR_MASK_REG_MINTU = 1;
   parameter ERR_MASK_REG_MTU   = 1;
   parameter ERR_MASK_REG_MAC   = 1;
    // Set Minimum frame length allowed and Frame MTU
   parameter MINTU              = 64;
   parameter MTU                = 1526;
    // Set MAC address check mode
   parameter MAC_CHECK_MODE     = 3;
    // Set number of allowed MAC unicast addresses (up to MACS parameter)
   parameter MAC_COUNT          = 10;

   // -------- XGMII TRANSACTION FORMAT --------------------------------------
    // XGMII packet size
   parameter XGMII_PACKET_SIZE_MAX       = 1526;
   parameter XGMII_PACKET_SIZE_MIN       = 64;
    // XGMII error enable/disable weights
   parameter XGMII_XGMII_ERR_EN_WT       = 0;
   parameter XGMII_XGMII_ERR_DIS_WT      = 1;
    // CRC error enable/disable weights
   parameter XGMII_CRC_ERR_EN_WT         = 1;
   parameter XGMII_CRC_ERR_DIS_WT        = 10;

   // -------- PACODAG TRANSACTION FORMAT ------------------------------------
    // Number of parts in one frame
   parameter PACODAG_PART_COUNT      = CTRL_HDR_EN + CTRL_FTR_EN;
    // Max size of parts
   int       PACODAG_PART_SIZE_MAX[] = '{64,64};
    // Min size of parts
   int       PACODAG_PART_SIZE_MIN[] = '{8,8};
   
   // -------- SAMPLING UNIT PARAMETERS --------------------------------------
    // Sampling enable/disable weights
   parameter SAU_SAMPLINGEN_WT          = 15;
   parameter SAU_SAMPLINGDIS_WT         = 1;

   // -------- XGMII DRIVER PARAMETERS ---------------------------------------
    // Delay enable/disable between transactions weight          
   parameter XGMII_DELAYEN_WT           = 1;  
   parameter XGMII_DELAYDIS_WT          = 5; 
    // Delay between transactions limits                    
   parameter XGMII_DELAYLOW             = 0; 
   parameter XGMII_DELAYHIGH            = 7; 

   // -------- PACODAG DRIVER PARAMETERS -------------------------------------
    // Pacodag data width
   parameter PACODAG_DATA_WIDTH         = FL_WIDTH_TX;
    // Delay enable/disable between transactions weight          
   parameter PACODAG_DELAYEN_WT         = 0;  
   parameter PACODAG_DELAYDIS_WT        = 50; 
    // Delay between transactions limits                    
   parameter PACODAG_DELAYLOW           = 0; 
   parameter PACODAG_DELAYHIGH          = 7; 
    // Delay enable/disable inside transaction weight          
   parameter PACODAG_INSIDE_DELAYEN_WT  = 0; 
   parameter PACODAG_INSIDE_DELAYDIS_WT = 50; 
    // Delay inside transaction limits                    
   parameter PACODAG_INSIDE_DELAYLOW    = 0; 
   parameter PACODAG_INSIDE_DELAYHIGH   = 7;                     

   // -------- FL MONITOR PARAMETERS -----------------------------------------
    // FL data width
   parameter MONITOR0_DATA_WIDTH         = FL_WIDTH_TX;
    // FL REM width 
   parameter MONITOR0_DREM_WIDTH         = FL_REM_WIDTH_TX;
    // Delay enable/disable between transactions weight          
   parameter MONITOR0_DELAYEN_WT         = 0;  
   parameter MONITOR0_DELAYDIS_WT        = 5; 
    // Delay between transactions limits                    
   parameter MONITOR0_DELAYLOW           = 0; 
   parameter MONITOR0_DELAYHIGH          = 7; 
    // Delay enable/disalbe inside transaction weight          
   parameter MONITOR0_INSIDE_DELAYEN_WT  = 0; 
   parameter MONITOR0_INSIDE_DELAYDIS_WT = 5; 
    // Delay inside transaction limits                    
   parameter MONITOR0_INSIDE_DELAYLOW    = 0; 
   parameter MONITOR0_INSIDE_DELAYHIGH   = 7;                     

endpackage
