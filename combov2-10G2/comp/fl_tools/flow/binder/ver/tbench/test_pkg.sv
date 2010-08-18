/*
 * test_pkg.sv: FL_BINDER Test package
 * Copyright (C) 2008 CESNET
 * Author(s): Martin Kosek <kosek@liberouter.org>
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
 * $Id: test_pkg.sv 12830 2010-02-17 02:31:45Z xsanta06 $
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package test_pkg;

  import math_pkg::*; // log2()

  // standard SystemVerilog Scoreboard
  `include "scoreboard.sv"
  
  // FL_BINDER GENERICS
  parameter INPUT_COUNT       = 2;
  parameter INPUT_WIDTH       = 64;
  parameter INPUT_DREM_WIDTH  = log2(INPUT_WIDTH/8);
  parameter OUTPUT_WIDTH      = 64;
  parameter OUTPUT_DREM_WIDTH = log2(OUTPUT_WIDTH/8);
  parameter FRAME_PARTS       = 3;

  parameter LUT_MEMORY        = 0;
  parameter LUT_BLOCK_SIZE    = 16;       // INPUT_WIDTH*INPUT_COUNT wide
  parameter SIMPLE_BINDER     = 0;
  parameter STUPID_BINDER     = 0;

  // CLOCKS AND RESETS
  parameter CLK_PERIOD = 10ns;
  parameter RESET_TIME = 10*CLK_PERIOD;

  // TRANSACTION FORMAT
  parameter GENERATOR_FL_PACKET_COUNT      = FRAME_PARTS;   // pocet paketov vo frame
  int       GENERATOR_FL_PACKET_SIZE_MAX[] = '{32,1526,32};   // maximalna velkost paketov
  int       GENERATOR_FL_PACKET_SIZE_MIN[] = '{8,64,8};      // minimalna velkost paketov

  // TEST SETTINGS
  parameter TEST_TRANSACTION_COUNT     = 1500;

  // DRIVER0 PARAMETERS
  parameter DRIVER_DATA_WIDTH          = INPUT_WIDTH;      // datova sirka driveru
  parameter DRIVER_DREM_WIDTH          = INPUT_DREM_WIDTH;      // drem sirka driveru
  parameter DRIVER_DELAYEN_WT          = 0;                  // vaha delay enable medzi transakciami
  parameter DRIVER_DELAYDIS_WT         = 3;                  // vaha delay disable medzi transakciami
  parameter DRIVER_DELAYLOW            = 0;                  // spodna hranica delay medzi transakciami
  parameter DRIVER_DELAYHIGH           = 3;                  // horna hranica delay medzi transakciami
  parameter DRIVER_INSIDE_DELAYEN_WT   = 0;                  // vaha delay enable v transakcii
  parameter DRIVER_INSIDE_DELAYDIS_WT  = 3;                  // vaha delay disable v transakcii
  parameter DRIVER_INSIDE_DELAYLOW     = 0;                  // spodna hranica delay v transakcii
  parameter DRIVER_INSIDE_DELAYHIGH    = 3;                  // horna hranica delay v transakcii

  // MONITOR PARAMETERS
  parameter MONITOR_DATA_WIDTH         = OUTPUT_WIDTH;     // datova sirka monitoru
  parameter MONITOR_DREM_WIDTH         = OUTPUT_DREM_WIDTH;     // drem sirka monitoru
  parameter MONITOR_DELAYEN_WT         = 0;                 // vaha delay enable medzi transakciami 
  parameter MONITOR_DELAYDIS_WT        = 3;                 // vaha delay disable medzi transakciami
  parameter MONITOR_DELAYLOW           = 0;                 // spodna hranica delay medzi transakciami
  parameter MONITOR_DELAYHIGH          = 3;                 // horna hranica delay medzi transakciami
  parameter MONITOR_INSIDE_DELAYEN_WT  = 0;                 // vaha delay enable v transakcii 
  parameter MONITOR_INSIDE_DELAYDIS_WT = 3;                 // vaha delay disable v transakcii
  parameter MONITOR_INSIDE_DELAYLOW    = 0;                 // spodna hranica delay v transakcii
  parameter MONITOR_INSIDE_DELAYHIGH   = 3;                 // horna hranica delay v transakcii

endpackage
