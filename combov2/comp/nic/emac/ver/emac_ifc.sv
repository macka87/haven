/*
 * emac_ifc.sv: EMAC Interface
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
 * $Id: emac_ifc.sv 15032 2010-08-13 07:29:34Z xsanta06 $
 *
 * TODO:
 *
 */
 

// ----------------------------------------------------------------------------
//                         EMAC RX Interface declaration
// ----------------------------------------------------------------------------
import math_pkg::*;

// -- EMAC RX Interface -------------------------------------------------------
interface iEmacRx (input logic CLK, RESET);  
  logic [7:0] DATA          = 'x;  // Data
  logic       DVLD          = 0;   // Data Valid
  logic       GOODFRAME     = 0;   // Good Frame
  logic       BADFRAME      = 0;   // Bad Frame
  logic       FRAMEDROP     = 0;   // Frame Drop
  logic [6:0] STATS         = 'x;  // Stats
  logic       STATSVLD      = 0;   // Stats Valid
  logic       STATSBYTEVLD  = 0;   // Stats Byte Valid

  // Clocking block
  clocking cb @(posedge CLK);
    output DATA, DVLD, GOODFRAME, BADFRAME, FRAMEDROP, 
           STATS, STATSVLD, STATSBYTEVLD;  
  endclocking: cb;

  // Modports
  modport dut (input DATA,
               input DVLD,
               input GOODFRAME,
               input BADFRAME,
               input FRAMEDROP,
               input STATS,
               input STATSVLD,
               input STATSBYTEVLD);
  
  modport tb (clocking cb);

endinterface : iEmacRx

// -- EMAC TX Interface -------------------------------------------------------
interface iEmacTx (input logic CLK, RESET);  
  logic [7:0] DATA             ;   // Data
  logic       DVLD             ;   // Data Valid
  logic       ACK           = 0;   // Ack
  logic       FIRSTBYTE        ;   // First Byte
  logic       UNDERRUN         ;   // Under run
  logic       COLLISION     = 0;   // Collision
  logic       RETRANSMIT    = 0;   // Retransmit
  logic [7:0] IFGDELAY         ;   // IFG Delay
  logic       SPEEDIS10100  = 0;   // Speed is 10/100
  logic       STATS         = 'x;  // Stats
  logic       STATSVLD      = 0;   // Stats Valid
  logic       STATSBYTEVLD  = 0;   // Stats Byte Valid

  // Clocking block
  clocking cb @(posedge CLK);
    input  DATA, DVLD, FIRSTBYTE, UNDERRUN, IFGDELAY;
    output ACK, COLLISION, RETRANSMIT, STATS, STATSVLD, STATSBYTEVLD;  
  endclocking: cb;

  // Modports
  modport dut (output DATA,
               output DVLD,
               input  ACK,
               output FIRSTBYTE,
               output UNDERRUN,
               input  COLLISION,
               input  RETRANSMIT,
               output IFGDELAY,
               input  SPEEDIS10100,
               input  STATS,
               input  STATSVLD,
               input  STATSBYTEVLD);
  
  modport tb (clocking cb);

endinterface : iEmacTx

