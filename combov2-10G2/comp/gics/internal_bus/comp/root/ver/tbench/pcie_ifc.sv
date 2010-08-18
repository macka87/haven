// pcie_ifc.sv: System Verilog PCI Express interface
// Copyright (C) 2007 CESNET
// Author(s): Tomas Malek <tomalek@liberouter.org>
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in
//    the documentation and/or other materials provided with the
//    distribution.
// 3. Neither the name of the Company nor the names of its contributors
//    may be used to endorse or promote products derived from this
//    software without specific prior written permission.
//
// This software is provided ``as is'', and any express or implied
// warranties, including, but not limited to, the implied warranties of
// merchantability and fitness for a particular purpose are disclaimed.
// In no event shall the company or contributors be liable for any
// direct, indirect, incidental, special, exemplary, or consequential
// damages (including, but not limited to, procurement of substitute
// goods or services; loss of use, data, or profits; or business
// interruption) however caused and on any theory of liability, whether
// in contract, strict liability, or tort (including negligence or
// otherwise) arising in any way out of the use of this software, even
// if advised of the possibility of such damage.
//
// $Id: pcie_ifc.sv 4278 2008-08-03 11:42:12Z xkobie00 $
//

// ----------------------------------------------------------------------------
//                        Interface declaration
// ----------------------------------------------------------------------------

// -- PCIE RX Interface -------------------------------------------------------
interface iPcieRx (input logic CLK, RESET);
  logic [ 6:0] BAR_HIT_N;
  logic            SOF_N;
  logic            EOF_N;
  logic [63:0]      DATA;
  logic [ 7:0]     REM_N;
  logic        SRC_RDY_N; 
  logic        DST_RDY_N; 

  logic        ERR_FWD_N; 
  logic          NP_OK_N;   
  logic  CPL_STREAMING_N;
  logic        SRC_DSC_N; 

  logic [11:0]  FC_PD_AV;
  logic [11:0] FC_NPD_AV;
  logic [ 7:0]  FC_PH_AV;
  logic [ 7:0] FC_NPH_AV;

  // Clocking block cb_driver
  clocking cb_driver @(posedge CLK);
     default output #3ns;
     input  DST_RDY_N, NP_OK_N, CPL_STREAMING_N;
     output SOF_N, EOF_N, DATA, REM_N, SRC_RDY_N, SRC_DSC_N, ERR_FWD_N, BAR_HIT_N, FC_PH_AV, FC_PD_AV, FC_NPH_AV, FC_NPD_AV;
  endclocking: cb_driver;
 
  modport dut (
     input  SOF_N, EOF_N, DATA, REM_N, SRC_RDY_N, SRC_DSC_N, ERR_FWD_N, BAR_HIT_N, FC_PH_AV, FC_PD_AV, FC_NPH_AV, FC_NPD_AV,
     output DST_RDY_N, NP_OK_N, CPL_STREAMING_N
     );

  // Driver (BFM) Modport
  modport driver (clocking cb_driver);
 
endinterface

// -- PCIE TX Interface -------------------------------------------------------
interface iPcieTx (input logic CLK, RESET);
   
  logic        LNK_UP_N;
  logic [63:0] TD;
  logic [7:0]  REM_N;
  logic        SOF_N;
  logic        EOF_N;
  logic        SRC_RDY_N;
  logic        DST_RDY_N;
  logic        SRC_DSC_N;
  logic        ERRFWD_N;
  logic        DST_DSC_N;
  logic [2:0]  BUF_AV;

  // Clocking block cb_monitor
  clocking cb_monitor @(posedge CLK);
    input LNK_UP_N, DST_RDY_N, DST_DSC_N, BUF_AV, TD,
          REM_N, SOF_N, EOF_N, SRC_RDY_N, SRC_DSC_N, ERRFWD_N;
  endclocking: cb_monitor;

  // Clocking block cb_responder
  clocking cb_responder @(posedge CLK);
    default output #3ns;
    output LNK_UP_N, DST_RDY_N, DST_DSC_N, BUF_AV;
    input  TD, REM_N, SOF_N, EOF_N, SRC_RDY_N, SRC_DSC_N, ERRFWD_N;
  endclocking: cb_responder;

  // Design Modport
  modport dut (
    input LNK_UP_N, DST_RDY_N, DST_DSC_N, BUF_AV,
    output TD, REM_N, SOF_N, EOF_N, SRC_RDY_N, SRC_DSC_N, ERRFWD_N
  );

  // Monitor (BFM) Modport
  modport monitor (clocking cb_monitor);

  // Responder (BFM) Modport
  modport responder (clocking cb_responder);

endinterface

// -- PCIE Configuration Interface --------------------------------------------
interface iPcieCfg (input logic CLK, RESET);
	logic [31:0] DO;
  logic        RD_WR_DONE_N;
  logic [31:0] DI;
  logic [9:0]  DWADDR;
  logic        WR_EN_N;
  logic        RD_EN_N;
 	logic        INTERRUPT_N;
  logic        INTERRUPT_RDY_N;
  logic [2:0]  INTERRUPT_MMENABLE;
  logic        INTERRUPT_MSIENABLE;
  logic [7:0]  INTERRUPT_DI;
  logic [7:0]  INTERRUPT_DO;
  logic	       INTERRUPT_ASSERT_N;
  logic	       TO_TURNOFF_N;
  logic	[3:0]  BYTE_EN_N;
  logic	[7:0]  BUS_NUMBER;
  logic	[4:0]  DEVICE_NUMBER;
  logic	[2:0]  FUNCTION_NUMBER;
  logic	[15:0] STATUS;
  logic	[15:0] COMMAND;
  logic	[15:0] DSTATUS;
  logic	[15:0] DCOMMAND;
  logic	[15:0] LSTATUS;
  logic	[15:0] LCOMMAND;
  logic        PM_WAKE_N;
  logic	[2:0]  PCIE_LINK_STATE_N;
  logic	       TRN_PENDING_N;
  logic [63:0] DSN;
  logic	       ERR_ECRC_N;
  logic	       ERR_UR_N;
  logic	       ERR_CPL_TIMEOUT_N;
  logic	       ERR_CPL_UNEXPECT_N;
  logic	       ERR_CPL_ABORT_N;
  logic	       ERR_POSTED_N;
  logic	       ERR_COR_N;
  logic	[47:0] ERR_TLP_CPL_HEADER;
  logic	       ERR_CPL_RDY_N;


  // Clocking block cb_driver
  clocking cb_driver @(posedge CLK);
    output DO, RD_WR_DONE_N, INTERRUPT_RDY_N, INTERRUPT_MMENABLE,
           INTERRUPT_MSIENABLE, INTERRUPT_DO, TO_TURNOFF_N,
           BUS_NUMBER, DEVICE_NUMBER, FUNCTION_NUMBER, STATUS,
           COMMAND, DSTATUS, DCOMMAND, LSTATUS, LCOMMAND,
           PCIE_LINK_STATE_N, ERR_CPL_RDY_N; 
    input  DI, DWADDR, WR_EN_N, RD_EN_N, INTERRUPT_N,
           INTERRUPT_DI, INTERRUPT_ASSERT_N, BYTE_EN_N,
           PM_WAKE_N, TRN_PENDING_N, DSN, ERR_ECRC_N,
           ERR_UR_N, ERR_CPL_TIMEOUT_N, ERR_CPL_UNEXPECT_N,
           ERR_CPL_ABORT_N, ERR_POSTED_N, ERR_COR_N, 
           ERR_TLP_CPL_HEADER;
  endclocking: cb_driver;

  modport dut (
    input  DO, RD_WR_DONE_N, INTERRUPT_RDY_N, INTERRUPT_MMENABLE,
           INTERRUPT_MSIENABLE, INTERRUPT_DO, TO_TURNOFF_N,
           BUS_NUMBER, DEVICE_NUMBER, FUNCTION_NUMBER, STATUS,
           COMMAND, DSTATUS, DCOMMAND, LSTATUS, LCOMMAND,
           PCIE_LINK_STATE_N, ERR_CPL_RDY_N,
    output DI, DWADDR, WR_EN_N, RD_EN_N, INTERRUPT_N,
           INTERRUPT_DI, INTERRUPT_ASSERT_N, BYTE_EN_N,
           PM_WAKE_N, TRN_PENDING_N, DSN, ERR_ECRC_N,
           ERR_UR_N, ERR_CPL_TIMEOUT_N, ERR_CPL_UNEXPECT_N,
           ERR_CPL_ABORT_N, ERR_POSTED_N, ERR_COR_N, 
           ERR_TLP_CPL_HEADER
  );

  // Driver (BFM) Modport
  modport driver (clocking cb_driver);

endinterface

