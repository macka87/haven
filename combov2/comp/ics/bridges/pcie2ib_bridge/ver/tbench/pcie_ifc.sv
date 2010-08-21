//
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
// $Id: pcie_ifc.sv 688 2007-10-19 16:11:56Z tomalek $
//

// ----------------------------------------------------------------------------
//                        Interface declaration
// ----------------------------------------------------------------------------

// -- PCIE RX Interface -------------------------------------------------------
interface iPcieRx (input logic CLK, RESET);
  logic SOF_N;
  logic EOF_N;
      
  logic [63:0] DATA;
  logic [ 7:0] REM_N;
      
  logic SRC_RDY_N; 
  logic DST_RDY_N; 

  logic SRC_DSC_N; 
  logic ERR_FWD_N; 
  logic NP_OK_N;   

  logic [ 6:0] BAR_HIT_N;

  logic [ 7:0] FC_PH_AV;
  logic [11:0] FC_PD_AV;
  logic [ 7:0] FC_NPH_AV;
  logic [11:0] FC_NPD_AV;

 
  modport bridge (
     input  CLK, RESET, SOF_N, EOF_N, DATA, REM_N, SRC_RDY_N, SRC_DSC_N, ERR_FWD_N, BAR_HIT_N, FC_PH_AV, FC_PD_AV, FC_NPH_AV, FC_NPD_AV,
     output DST_RDY_N, NP_OK_N
     );

  modport driver (
     input  CLK, RESET, DST_RDY_N, NP_OK_N,
     output SOF_N, EOF_N, DATA, REM_N, SRC_RDY_N, SRC_DSC_N, ERR_FWD_N, BAR_HIT_N, FC_PH_AV, FC_PD_AV, FC_NPH_AV, FC_NPD_AV
  );
 
endinterface

// -- PCIE TX Interface -------------------------------------------------------
interface iPcieTx (input logic CLK, RESET);
  logic SOF_N;
  logic EOF_N;
             
  logic [63:0] DATA;  
  logic [ 7:0] REM_N; 
             
  logic SRC_RDY_N;
  logic DST_RDY_N;
                                                                                                                                                                 
  logic SRC_DCS_N;
  logic DST_DCS_N;
                                                                                                                                                                
  logic [ 2:0] BUF_AV;

  modport bridge (
    input  CLK, RESET, DST_RDY_N, DST_DCS_N, BUF_AV,
    output SOF_N, EOF_N, SRC_RDY_N, DATA, REM_N, SRC_DCS_N
  );

  modport monitor (
      input  CLK, RESET, SOF_N, EOF_N, SRC_RDY_N, DATA, REM_N, SRC_DCS_N,
      output DST_RDY_N, DST_DCS_N, BUF_AV
  );

endinterface

// -- PCIE Configuration Interface --------------------------------------------
interface iPcieCfg (input logic CLK, RESET);
  logic [7:0] BUS_NUM;
  logic [4:0] DEVICE_NUM;
  logic [2:0] FUNC_NUM;  
  logic [2:0] MAX_PAYLOAD_SIZE;

  modport bridge (
    input  BUS_NUM, DEVICE_NUM, FUNC_NUM, MAX_PAYLOAD_SIZE    
  );

  modport driver (
    output  BUS_NUM, DEVICE_NUM, FUNC_NUM, MAX_PAYLOAD_SIZE    
  );


endinterface

