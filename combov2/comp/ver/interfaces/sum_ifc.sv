/*
 * sum_ifc.sv: Status Update Manager Interface
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
 * $Id: sum_ifc.sv 10489 2009-08-18 14:25:25Z xsanta06 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//             SUM Interface declaration
// ----------------------------------------------------------------------------

interface iSum #(FLOWS=4, BLOCK_SIZE = 4) (input logic CLK, RESET);  

  import math_pkg::*;       // log2()    
 
  //-- Signals ----------------------------------------------------------------

  // SUM misc interface
  logic [2*FLOWS-1:0]                  INTERRUPT       ;                 
  logic [2*FLOWS-1:0]                  IDLE            ;          
  logic [2*FLOWS-1:0]                  FLUSH        = 0;                 
  logic [2*FLOWS-1:0]                  INIT         = 0;                 
  // RX Request Fifo interface
  logic [abs(log2(FLOWS)-1):0]         RX_RF_RADDR     ;
  logic [log2(BLOCK_SIZE)+64:0]        RX_RF_DOUT   = 0;
  logic                                RX_RF_DVLD   = 0;             
  logic [FLOWS-1:0]                    RX_RF_EMPTY  = 0;
  logic                                RX_RF_READ      ;             
  logic [log2(BLOCK_SIZE+1)*FLOWS-1:0] RX_RF_STATUS = 0;

  //-- Clocking Blocks -------------------------------------------------------- 
  
  // Status Clocking Block 
    clocking misc_cb @(posedge CLK);
     input  INTERRUPT, IDLE;
     output FLUSH, INIT;
    endclocking: misc_cb 

  // RX Request Fifo Clocking Block 
    clocking reqFifo_cb @(posedge CLK);
     output RX_RF_DOUT, RX_RF_DVLD, RX_RF_EMPTY, RX_RF_STATUS;
     input  RX_RF_RADDR, RX_RF_READ;
    endclocking: reqFifo_cb 

  //-- Modports ---------------------------------------------------------------
 
  // Misc Modport
    modport misc_dut    (output INTERRUPT,
                         output IDLE,
                         input  FLUSH,
                         input  INIT);
  // RX Request FIFO Modport
    modport reqFifo_dut (input  RX_RF_DOUT,
                         input  RX_RF_DVLD,
                         input  RX_RF_EMPTY,
                         input  RX_RF_STATUS,
                         output RX_RF_RADDR,
                         output RX_RF_READ);
                      
  //-- TB Modports ----------------------------------------------------
   modport misc_tb    (clocking misc_cb);
   modport reqFifo_tb (clocking reqFifo_cb);

  endinterface : iSum
  
// ----------------------------------------------------------------------------
//             Status Update Interface declaration
// ----------------------------------------------------------------------------

interface iSu #(FLOWS = 4, DATA_SIZE = 8) (input logic CLK, RESET);  

  import math_pkg::*;       // log2()    
 
  //-- Signals ----------------------------------------------------------------
  logic [log2(FLOWS)-1:0]          SU_ADDR  = 0;
  logic [DATA_SIZE-1:0]            SU_DATA  = 0;
  logic                            SU_DVLD  = 0;             
  logic [FLOWS-1:0]                SU_HFULL    ;

  //-- Clocking Blocks -------------------------------------------------------- 
  // Status Clocking Block 
    clocking su_cb @(posedge CLK);
     output SU_ADDR, SU_DATA, SU_DVLD;
     input  SU_HFULL;
    endclocking: su_cb;  

  //-- Modports ---------------------------------------------------------------
  // Status Update Modport
    modport su_dut  (input  SU_ADDR,
                     input  SU_DATA,
                     input  SU_DVLD,
                     output SU_HFULL);                      
                       
  //-- TB Modports ----------------------------------------------------
   modport su_tb    (clocking su_cb);

  endinterface : iSu

