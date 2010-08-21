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
 * $Id: test_pkg.sv 14063 2010-06-16 12:35:47Z xsanta06 $
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

   /*
    * RX A => TX A
    * RX B => TX C
    * RX C => TX D
    * RX D => TX B
    */
   parameter MI32_DATA_1    = 32'h009C;

   /*
    * RX A => TX A
    * RX A => TX B
    * RX A => TX C
    * RX B => TX D
    */
   parameter MI32_DATA_2    = 32'h0040;
   parameter MI32_ADDRESS   = 32'h0080;

   // -------- DUT PARAMETERS ------------------------------------------------
   parameter XGMII_COUNT = 4;

   // -------- TEST PARAMETERS -----------------------------------------------
    // Count of transactions to generate
   parameter TRANSACTION_COUNT = 1000;

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

  // -------- XGMII DRIVER PARAMETERS ---------------------------------------
    // Delay enable/disable between transactions weight          
   parameter XGMII_DELAYEN_WT           = 1;  
   parameter XGMII_DELAYDIS_WT          = 5; 
    // Delay between transactions limits                    
   parameter XGMII_DELAYLOW             = 0; 
   parameter XGMII_DELAYHIGH            = 7; 


endpackage
