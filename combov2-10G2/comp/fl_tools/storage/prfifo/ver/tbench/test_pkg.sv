/*
 * test_pkg.sv: Test package
 * Copyright (C) 2007 CESNET
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
 * $Id: test_pkg.sv 11280 2009-09-23 11:50:43Z xsanta06 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package test_pkg;

   import math_pkg::*; // log2

   // Scoreboard and Discarding model files
   `include "scoreboard.sv"
   `include "fl_prfifo_discarding_model.sv"
   
   // DUT GENERICS
   parameter MEM_TYPE   = 0;             // memory type (0 = LUT, 1 = BRAM)
   parameter DATA_WIDTH = 128;            // data width
   parameter ITEMS      = 10;            // maximum items the FIFO can contain 
   parameter PARTS      = 0;             // 0 - autodetect; 1,2,3 - Given value

   parameter DREM_WIDTH = log2(DATA_WIDTH/8); // drem width
   
   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TRANSACTION FORMAT (GENERATOR 0)
   parameter GENERATOR0_FL_PACKET_COUNT      = 2;                // pocet paketov vo frame
   int       GENERATOR0_FL_PACKET_SIZE_MAX[] = '{64, 200};      // maximalna velkost paketov
   int       GENERATOR0_FL_PACKET_SIZE_MIN[] = '{8, 50};         // minimalna velkost paketov

   // DRIVER0 PARAMETERS
   parameter DRIVER0_DATA_WIDTH         = DATA_WIDTH;         // datova sirka driveru
   parameter DRIVER0_DREM_WIDTH         = DREM_WIDTH;         // drem sirka driveru
   parameter DRIVER0_DELAYEN_WT         = 1;                     // vaha delay enable medzi transakciami
   parameter DRIVER0_DELAYDIS_WT        = 5;                     // vaha delay disable medzi transakciami
   parameter DRIVER0_DELAYLOW           = 0;                     // spodna hranica delay medzi transakciami
   parameter DRIVER0_DELAYHIGH          = 10;                     // horna hranica delay medzi transakciami
   parameter DRIVER0_INSIDE_DELAYEN_WT  = 1;                     // vaha delay enable v transakcii
   parameter DRIVER0_INSIDE_DELAYDIS_WT = 5;                     // vaha delay disable v transakcii
   parameter DRIVER0_INSIDE_DELAYLOW    = 0;                     // spodna hranica delay v transakcii
   parameter DRIVER0_INSIDE_DELAYHIGH   = 10;                     // horna hranica delay v transakcii

   // MONITOR0 PARAMETERS
   parameter MONITOR0_DATA_WIDTH         = DATA_WIDTH;         // datova sirka monitoru
   parameter MONITOR0_DREM_WIDTH         = DREM_WIDTH;         // drem sirka monitoru
   parameter MONITOR0_DELAYEN_WT         = 3;                     // vaha delay enable medzi transakciami 
   parameter MONITOR0_DELAYDIS_WT        = 15;                     // vaha delay disable medzi transakciami
   parameter MONITOR0_DELAYLOW           = 25;                     // spodna hranica delay medzi transakciami
   parameter MONITOR0_DELAYHIGH          = 50;                     // horna hranica delay medzi transakciami
   parameter MONITOR0_INSIDE_DELAYEN_WT  = 3;                     // vaha delay enable v transakcii 
   parameter MONITOR0_INSIDE_DELAYDIS_WT = 15;                     // vaha delay disable v transakcii
   parameter MONITOR0_INSIDE_DELAYLOW    = 25;                     // spodna hranica delay v transakcii
   parameter MONITOR0_INSIDE_DELAYHIGH   = 50;                     // horna hranica delay v transakcii


   // TEST PARAMETERS
   parameter TRANSACTION_COUNT = 10000; // Count of transactions to generate

endpackage
