/*
 * ibuf_ifc.sv: IBUF Interface
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
 * $Id: ibuf_ifc.sv 12330 2009-12-24 01:07:54Z xsanta06 $
 *
 * TODO:
 *
 */
 

// ----------------------------------------------------------------------------
//                       XGMII IBUF Interface declaration
// ----------------------------------------------------------------------------
import math_pkg::*;

// -- Sampling Unit Interface -----------------------------------------------------
interface iSamplingUnit (input logic CLK, RESET);  
  logic REQ               ;  // Request for sampling information
  logic ACCEPT         = 0;  // Accept incoming frame
  logic DV             = 0;  // Sampling information valid
  

  clocking cb @(posedge CLK);
    output ACCEPT, DV;
    input  REQ;  
  endclocking: cb;
  
  // Receive Modport
  modport dut ( output REQ,
                input  ACCEPT,
                input  DV);
  
  // Transitive Modport
  modport tb (clocking cb);
  
endinterface : iSamplingUnit

// -- Link State Interface -----------------------------------------------------
interface iLinkState (input logic CLK, RESET);  
  logic LINK;                 // Active when link is up
  logic INCOMING_PCKT;        // Active when a packet is being received
  

  clocking cb @(posedge CLK);
    input  LINK, INCOMING_PCKT;  
  endclocking: cb;
  
  // Receive Modport
  modport dut ( output LINK,
                output INCOMING_PCKT);
  
  // Transitive Modport
  modport tb (clocking cb);
  
endinterface : iLinkState
