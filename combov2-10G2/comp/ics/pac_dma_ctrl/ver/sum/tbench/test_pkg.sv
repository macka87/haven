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
 * $Id: test_pkg.sv 12303 2009-12-17 09:46:41Z kastovsky $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package test_pkg;
   
   import math_pkg::*;
   
   // == DUT GENERICS ==
   parameter FLOWS            = 2;  // Number of connected ctrls
   parameter BLOCK_SIZE       = 32;  // Max number of descriptors in one transfer
                                       // size of transfer is BLOCK_SIZE*16
   parameter BASE_ADDR        = 0;  // Base address of the TX buffer
   parameter DMA_ID           = 1;  // Tag to identify DMA component
   parameter DMA_DATA_WIDTH   = 32; // Data width of DMA requests
   parameter NFIFO_LUT_MEMORY = 0;  // Use lut memory type in nfifo
   
   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TESTBENCH PARAMETERS
   parameter TX_SU_DATA_SIZE = 8;
   parameter RX_SU_DATA_SIZE = 24;
   parameter TX_GADDR        = 'h12345678DEADBEEF;
   parameter TRANS_TYPE      = 1;
   parameter SEED            = 1337;
   
   // TRANSACTION FORMAT
   // Probability of setting INTF or LFF
   // RX update
   // Probability of setting INTF (INTF1_WT : INTF0_WT)
   parameter RX_UPDATE_INTF0_WT         = 10;  
   parameter RX_UPDATE_INTF1_WT         = 1; 
   // Probability of setting LFF (LFF1_WT : LFF0_WT)
   parameter RX_UPDATE_LFF0_WT          = 0; 
   parameter RX_UPDATE_LFF1_WT          = 1; 
   // TX update
   // Probability of setting INTF (INTF1_WT : INTF0_WT)
   parameter TX_UPDATE_INTF0_WT         = 10; 
   parameter TX_UPDATE_INTF1_WT         = 1; 
   // Probability of setting LFF (LFF1_WT : LFF0_WT)
   parameter TX_UPDATE_LFF0_WT          = 1; 
   parameter TX_UPDATE_LFF1_WT          = 15;                     

   // DRIVER PARAMETERS
   // RX SU DRIVER PARAMETERS
   // Weight of DVLD delay enable
   parameter RX_SU_DRIVER_DELAYEN_WT    = 1; 
   // Weight of DVLD delay disable
   parameter RX_SU_DRIVER_DELAYDIS_WT   = 0;
   // Low boundary DVLD delay
   parameter RX_SU_DRIVER_DELAYLOW      = 8;
   // High boundary DVLD delay
   parameter RX_SU_DRIVER_DELAYHIGH     = 192;

   // TX SU DRIVER PARAMETERS
   // Weight of DVLD delay enable
   parameter TX_SU_DRIVER_DELAYEN_WT    = 1; 
   // Weight of DVLD delay disable
   parameter TX_SU_DRIVER_DELAYDIS_WT   = 0;
   // Low boundary DVLD delay
   parameter TX_SU_DRIVER_DELAYLOW      = 8;
   // High boundary DVLD delay
   parameter TX_SU_DRIVER_DELAYHIGH     = 192;

   // RX RF DRIVER PARAMETERS
   // Weight of DVLD delay enable
   parameter RF_DRIVER_DELAYEN_WT       = 1; 
   // Weight of DVLD delay disable
   parameter RF_DRIVER_DELAYDIS_WT      = 3;
   // Low boundary DVLD delay
   parameter RF_DRIVER_DELAYLOW         = 3;
   // High boundary DVLD delay
   parameter RF_DRIVER_DELAYHIGH        = 7;

   // TIMEOUT MODULE PARAMETERS
   // Low boundary timeout
   parameter TIMEOUT_LOW                = 500;
   // High boundary timeout
   parameter TIMEOUT_HIGH               = 1000;

   // MONITOR PARAMETERS
   // Monitor data width
   parameter MONITOR0_DATA_WIDTH        = 64;

   // TEST PARAMETERS
   parameter RX_STATUS_UPDATE_COUNT = 1000;// Count of transactions to generate
   parameter TX_STATUS_UPDATE_COUNT = 1000;// Count of transactions to generate

endpackage
