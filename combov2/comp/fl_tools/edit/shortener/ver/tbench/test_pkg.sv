/*
 * test_pkg.sv: Test package
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobiersky <kobiersky@liberouter.org>
 *            Jan Stourac <xstour03@stud.fit.vutbr.cz>
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
 * $Id: test_pkg.sv 9356 2009-07-13 16:19:33Z xstour03 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package test_pkg;

   // Include this file if you want to use standard SystemVerilog Scoreboard
   `include "scoreboard.sv"
   
   // Include this file if you want to use C plus plus Scoreboard
   // `include "dpi/dpi_scoreboard.sv"

   // DUT GENERICS
   parameter RX_DATA_WIDTH = 32;            // datova sirka RX
   parameter RX_DREM_WIDTH = 2;             // drem  sirka RX
   parameter TX_DATA_WIDTH = 32;            // datova sirka TX
   parameter TX_DREM_WIDTH = 2;             // drem sirka TX
   parameter PART_NUM      = 0;             // number of part which is about to be shortened (0 = first part)
   parameter BYTES_KEPT    = 22;            // number of bytes to be left in shortened part
   parameter PARTS         = 1;             // number of parts in frame

   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TRANSACTION FORMAT (GENERATOR 0)
   parameter GENERATOR0_FL_PACKET_COUNT      = PARTS;            // number of parts in frame
   int       GENERATOR0_FL_PACKET_SIZE_MAX[] = '{650,650,650};   // maximal size of parts
   int       GENERATOR0_FL_PACKET_SIZE_MIN[] = '{1,1,1};         // minimal size of parts

   // DRIVER0 PARAMETERS
   parameter DRIVER0_DATA_WIDTH         = RX_DATA_WIDTH;         // driver data width
   parameter DRIVER0_DREM_WIDTH         = RX_DREM_WIDTH;         // driver drem width
   parameter DRIVER0_DELAYEN_WT         = 1;                     // vaha delay enable medzi transakciami
   parameter DRIVER0_DELAYDIS_WT        = 3;                     // vaha delay disable medzi transakciami
   parameter DRIVER0_DELAYLOW           = 0;                     // spodna hranica delay medzi transakciami
   parameter DRIVER0_DELAYHIGH          = 3;                     // horna hranica delay medzi transakciami
   parameter DRIVER0_INSIDE_DELAYEN_WT  = 1;                     // vaha delay enable v transakcii
   parameter DRIVER0_INSIDE_DELAYDIS_WT = 3;                     // vaha delay disable v transakcii
   parameter DRIVER0_INSIDE_DELAYLOW    = 0;                     // spodna hranica delay v transakcii
   parameter DRIVER0_INSIDE_DELAYHIGH   = 3;                     // horna hranica delay v transakcii

   // MONITOR0 PARAMETERS
   parameter MONITOR0_DATA_WIDTH         = TX_DATA_WIDTH;         // driver data width
   parameter MONITOR0_DREM_WIDTH         = TX_DREM_WIDTH;         // driver drem width
   parameter MONITOR0_DELAYEN_WT         = 1;                     // vaha delay enable medzi transakciami 
   parameter MONITOR0_DELAYDIS_WT        = 3;                     // vaha delay disable medzi transakciami
   parameter MONITOR0_DELAYLOW           = 0;                     // spodna hranica delay medzi transakciami
   parameter MONITOR0_DELAYHIGH          = 3;                     // horna hranica delay medzi transakciami
   parameter MONITOR0_INSIDE_DELAYEN_WT  = 1;                     // vaha delay enable v transakcii 
   parameter MONITOR0_INSIDE_DELAYDIS_WT = 3;                     // vaha delay disable v transakcii
   parameter MONITOR0_INSIDE_DELAYLOW    = 0;                     // spodna hranica delay v transakcii
   parameter MONITOR0_INSIDE_DELAYHIGH   = 3;                     // horna hranica delay v transakcii


   // TEST PARAMETERS
   parameter TRANSACTION_COUT = 20000; // Count of transactions to generate

endpackage
