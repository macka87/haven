/*
 * mi32_ifc.pkg: MI32 Interface
 * Copyright (C) 2008 CESNET
 * Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
 *            Petr Kastovsky <kastovsky@liberouter.org>
 *            Marek Santa <santa@liberouter.org>
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
 * $Id: mi32_ifc.sv 12663 2010-02-09 02:20:39Z xsanta06 $
 *
 * TODO:
 *
 */
 

// ----------------------------------------------------------------------------
//                         MI32 Interface declaration
// ----------------------------------------------------------------------------
// enum that defines local constants for mi32 interface
// -- MI32 Interface -----------------------------------------------------
interface iMi32 (input logic CLK, RESET);  
  logic [31:0] ADDR  = 0;  // ADDRess
  logic [31:0] DWR   = 0;  // Data to be WRitten
  logic [31:0] DRD;        // Data to be ReaD
  logic [3:0] BE     = 0;  // Byte Enable
  logic RD           = 0;  // ReaD request
  logic WR           = 0;  // WRite request
  logic ARDY;              // Address ReaDY
  logic DRDY;              // Data ReaDY
  
  //-- MI32 Clocking Blocks --------------------------------------------------- 
  clocking cb @(posedge CLK);
    input  ARDY, DRDY, DRD;
    output ADDR, DWR, BE, RD, WR;  
  endclocking: cb;

  clocking monitor_cb @(posedge CLK);
    input ADDR, DWR, DRD, BE, RD, WR, ARDY, DRDY;
  endclocking: monitor_cb;

  //-- MI32 Modports ----------------------------------------------------------
  modport dut (input  ADDR,
               input  DWR,
               input  BE,
               input  RD,
               input  WR,
               output ARDY,
               output DRDY,
               output DRD);
  
  // Driver Modport
  modport tb (clocking cb);

  // Monitor Modport
  modport monitor (clocking monitor_cb);
  
  // --------------------------------------------------------------------------
  // -- Interface properties/assertions
  // --------------------------------------------------------------------------

  // -- While RESET RD inactive ----------------------------------------
  // RD may be active only if RESET is inactive. 
  property RESETR;
     @(posedge CLK) (RESET)|->(not RD); 
  endproperty   
  
  assert property (RESETR)
     else $error("RD is active during reset.");

  // -- While RESET WR inactive ----------------------------------------
  // WR may be active only if RESET is inactive. 
  property RESETW;
     @(posedge CLK) (RESET)|->(not WR); 
  endproperty   
  
  assert property (RESETW)
     else $error("WR is active during reset.");
  
  // -- ARDY together with RD or WR -------------------------------------
  // ARDY must be active together with RD or WR.
  property ARDYWRRD;
     @(posedge CLK) (ARDY)|->(WR || RD); 
  endproperty
  
  assert property (ARDYWRRD)
     else $error("ARDY and WR or RD signals are not active at the same cycle.");
     
  // -- WR never together with RD ---------------------------------------
  // WR can not be active together with RD.
  property RDnottogetherWR;
     @(posedge CLK) (RD)|->(!WR); 
  endproperty
  
  assert property (RDnottogetherWR)
     else $error("RD and WR signals can not be active at the same cycle.");   
     
endinterface : iMi32
