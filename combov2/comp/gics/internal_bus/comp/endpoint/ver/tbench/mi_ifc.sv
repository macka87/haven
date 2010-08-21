/*
 * mi_ifc.sv: Memory Interface
 * Copyright (C) 2009 CESNET
 * Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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
 * $Id: mi_ifc.sv 8956 2009-06-24 21:16:49Z washek $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                       Memory Interface declaration
// ----------------------------------------------------------------------------

interface iMI #(int DATA_WIDTH = 32, int ADDR_WIDTH = 32) 
                                                      (input logic CLK, RESET);
  
  logic [DATA_WIDTH-1:0]   DWR;
  logic [ADDR_WIDTH-1:0]   ADDR;
  logic                    RD;
  logic                    WR;
  logic [DATA_WIDTH/8-1:0] BE;
  logic [DATA_WIDTH-1:0]   DRD;
  logic                    ARDY;
  logic                    DRDY;
  
  
  //-- Master Clocking Block --------------------------------------------------
  /*clocking master_cb @(posedge CLK);
    input DRD, ARDY, DRDY;
    output DWR, ADDR, RD, WR, BE;
  endclocking: master_cb;
  
  //-- Slave Clocking Block ---------------------------------------------------
  clocking slave_cb @(posedge CLK);
    input DWR, ADDR, RD, WR, BE;
    output DRD, ARDY, DRDY;
  endclocking: slave_cb;
    */ 
  //-- Master Modport ---------------------------------------------------------
  modport master (
    input  DRD, ARDY, DRDY,
    output DWR, ADDR, RD, WR, BE
  );
  
  //-- Slave Modport ----------------------------------------------------------
  modport slave (
    input  DWR, ADDR, RD, WR, BE,
    output DRD, ARDY, DRDY
  );
  
  //-- Transitive Modports ----------------------------------------------------
  //modport master_tb (clocking master_cb);
  //modport slave_tb  (clocking slave_cb);
  
  
  //---------------------------------------------------------------------------
  //-- Interface properties/assertions ----------------------------------------
  
  // -- While RESET RD inactive -----------------------------------------------
  property ResetRD;
     @(posedge CLK) (RESET)|->(not RD);
  endproperty
  
  assert property (ResetRD)
     else $error("RD is active during reset.");

  // -- While RESET WR inactive -----------------------------------------------
  property ResetWR;
     @(posedge CLK) (RESET)|->(not WR);
  endproperty
  
  assert property (ResetWR)
     else $error("WR is active during reset.");
  

  //-- BE mustn't be all zeros ------------------------------------------------
  property BENotZero;
    @(posedge CLK) (RD || WR) |=> (BE != 0);
  endproperty
  
  assert property (BENotZero)
    else $error("All bits of BE are zero while RD or WR is active.");
  
endinterface : iMI
