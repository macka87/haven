/*
 * xgmii_ifc.sv: XGMII Interface
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
 * $Id: xgmii_ifc.sv 13467 2010-04-09 07:46:47Z xsanta06 $
 *
 * TODO:
 *
 */
 

// ----------------------------------------------------------------------------
//                         XGMII RX Interface declaration
// ----------------------------------------------------------------------------
import math_pkg::*;

// -- XGMII DDR RX Interface --------------------------------------------------
interface iXgmiiDdrRx (input logic CLK, RESET);  
  logic [31:0] RXD          = 32'h07070707;  // Data
  logic [ 3:0] RXC          = '1;  // Control

  clocking cb @(posedge CLK or negedge CLK);
    output RXD, RXC;  
  endclocking: cb;

  // Receive Modport
  modport dut (input RXD,
               input RXC);
  
  // Transitive Modport
  modport tb (clocking cb);

endinterface : iXgmiiDdrRx

// -- XGMII SDR RX Interface --------------------------------------------------
interface iXgmiiSdrRx (input logic CLK, RESET);  
  logic [63:0] RXD          = 64'h0707070707070707;  // Data
  logic [ 7:0] RXC          = '1;  // Control

  clocking cb @(posedge CLK);
    output RXD, RXC;  
  endclocking: cb;

  // Receive Modport
  modport dut (input RXD,
               input RXC);
  
  // Transitive Modport
  modport tb (clocking cb);

endinterface : iXgmiiSdrRx

// -- XGMII DDR TX Interface --------------------------------------------------
interface iXgmiiDdrTx (input logic CLK, RESET);  
  logic [31:0] TXD;  // Data
  logic [ 3:0] TXC;  // Control

  clocking cb @(posedge CLK or negedge CLK);
    input TXD, TXC;  
  endclocking: cb;

  // Receive Modport
  modport dut (output TXD,
               output TXC);
  
  // Transitive Modport
  modport tb (clocking cb);

endinterface : iXgmiiDdrTx

// -- XGMII SDR TX Interface --------------------------------------------------
interface iXgmiiSdrTx (input logic CLK, RESET);  
  logic [63:0] TXD;  // Data
  logic [ 7:0] TXC;  // Control

  clocking cb @(posedge CLK);
    input TXD, TXC;  
  endclocking: cb;

  // Receive Modport
  modport dut (output TXD,
               output TXC);
  
  // Transitive Modport
  modport tb (clocking cb);

endinterface : iXgmiiSdrTx

