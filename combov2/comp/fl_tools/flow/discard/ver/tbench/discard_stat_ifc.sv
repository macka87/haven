/*
 * discard_stat_ifc.sv: FrameLink Discard Stat Interface
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
 * $Id: discard_stat_ifc.sv 14542 2010-07-21 07:23:31Z xsanta06 $
 *
 * TODO:
 *
 */
 

// ----------------------------------------------------------------------------
//                         FrameLink Interface declaration
// ----------------------------------------------------------------------------
import math_pkg::*; //log2

// -- FrameLink Discard Stat Interface ----------------------------------------
interface iDiscardStat #(CHANNELS=2, STATUS_WIDTH=2) (input logic CLK, RESET);  
  logic [log2(CHANNELS)-1:0] RX_CHAN        = 0;  // Input channel
  logic [CHANNELS-1:0]       DST_RDY_N         ;  // FL RX Destination Ready
  logic [log2(CHANNELS)-1:0] TX_CHAN           ;  // Output channel
  logic [CHANNELS*STATUS_WIDTH-1:0] STATUS     ;  // Status
  logic [CHANNELS*STATUS_WIDTH-1:0] BUF_STATUS ;  // Status

  clocking rx_cb @(posedge CLK);
    input  DST_RDY_N;
    output RX_CHAN;  
  endclocking: rx_cb

  clocking tx_cb @(posedge CLK);
    input TX_CHAN;  
  endclocking: tx_cb

  clocking stat_cb @(posedge CLK);
    output STATUS;  
    input  BUF_STATUS;  
  endclocking: stat_cb

  // DUT Modport
  modport dut (input  RX_CHAN,
               output DST_RDY_N,
               output TX_CHAN,
               input  STATUS,
               output BUF_STATUS);
  
  // Testbench Modports
  modport rx_tb   (clocking rx_cb);
  modport tx_tb   (clocking tx_cb);
  modport stat_tb (clocking stat_cb);

endinterface : iDiscardStat
