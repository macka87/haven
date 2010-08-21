/*
 * ctrl_ifc.pkg: Control Interface
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
 * $Id: ctrl_ifc.sv 10588 2009-08-21 09:02:15Z xsanta06 $
 *
 * TODO:
 *
 */
 

// ----------------------------------------------------------------------------
//                   Control Interface declaration
// ----------------------------------------------------------------------------

// -- Control Interface -------------------------------------------------------
interface iControl #(CTRL_DATA_WIDTH = 8) (input logic CLK, RESET);  
  // Input interface
  logic [CTRL_DATA_WIDTH-1:0] CTRL_DATA_IN = 0  ;  // Data
  logic CTRL_DATA_IN_VLD                   = 0  ;  // Valid signal
  logic CTRL_DATA_IN_RQ                         ;  // Request signal

  // Output interface
  logic [CTRL_DATA_WIDTH-1:0] CTRL_DATA_OUT     ;  // Data
  logic CTRL_DATA_OUT_VLD                       ;  // Valid signal
  logic CTRL_DATA_OUT_RQ                   = 0  ;  // Request signal

  // Clocking blocks
  clocking in_cb @(posedge CLK);
    input  CTRL_DATA_IN_RQ;
    output CTRL_DATA_IN, CTRL_DATA_IN_VLD;
  endclocking: in_cb;

  clocking out_cb @(posedge CLK);
    input  CTRL_DATA_OUT, CTRL_DATA_OUT_VLD;
    output CTRL_DATA_OUT_RQ;
  endclocking: out_cb;

  // Receive Modport
  modport dut_in (input  CTRL_DATA_IN,
                  input  CTRL_DATA_IN_VLD,
                  output CTRL_DATA_IN_RQ);
  
  modport dut_out (output CTRL_DATA_OUT,
                   output CTRL_DATA_OUT_VLD,
                   input  CTRL_DATA_OUT_RQ);

  // Testbench modports
  modport in_tb (clocking in_cb);
  modport out_tb (clocking out_cb);
    
endinterface : iControl
