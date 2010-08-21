/*
 * DUT.sv: Design under test
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
 * $Id: dut.sv 11602 2009-10-14 19:03:54Z xspinl00 $
 *
 * TODO:
 *
 */
 
// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module DUT (
   input logic               CLK,
   input logic               RESET,
   iInternalBusUp.ib_up      IBUP,
   iInternalBusDown.ib_down  IBDOWN,
   iFrameLinkRx.dut          FLRX[FLOWS],
   iFrameLinkTx.dut          FLTX[FLOWS],
   output logic              RX_INTERRUPT,
   output logic              TX_INTERRUPT
);

// Signals for DUT conection
// FrameLink Interface
wire [TXDWIDTH*FLOWS-1:0] tx_data;  
wire [FLOWS-1:0]      tx_sop_n;
wire [FLOWS-1:0]      tx_eop_n;
wire [FLOWS-1:0]      tx_sof_n;
wire [FLOWS-1:0]      tx_eof_n;
wire [TXDREMWIDTH*FLOWS-1:0] tx_rem;
wire [FLOWS-1:0]      tx_src_rdy_n;
wire [FLOWS-1:0]      tx_dst_rdy_n;

wire [RXDWIDTH*FLOWS-1:0] rx_data;  
wire [FLOWS-1:0]      rx_sop_n;
wire [FLOWS-1:0]      rx_eop_n;
wire [FLOWS-1:0]      rx_sof_n;
wire [FLOWS-1:0]      rx_eof_n;
wire [RXDREMWIDTH*FLOWS-1:0] rx_rem;
wire [FLOWS-1:0]      rx_src_rdy_n;
wire [FLOWS-1:0]      rx_dst_rdy_n;

// Connecting FR to interfaces
generate
for (genvar i=0; i<FLOWS; i++) begin  
  assign FLTX[i].DATA      = tx_data[(i+1)*TXDWIDTH-1:TXDWIDTH*i];
  assign FLTX[i].SOP_N     = tx_sop_n[i];
  assign FLTX[i].EOP_N     = tx_eop_n[i];
  assign FLTX[i].SOF_N     = tx_sof_n[i];
  assign FLTX[i].EOF_N     = tx_eof_n[i];
  assign FLTX[i].DREM      = tx_rem[(i+1)*TXDREMWIDTH-1:TXDREMWIDTH*i];
  assign FLTX[i].SRC_RDY_N = tx_src_rdy_n[i];
  assign tx_dst_rdy_n[i]   = FLTX[i].DST_RDY_N;
  
  assign rx_data[(i+1)*RXDWIDTH-1:RXDWIDTH*i]        = FLRX[i].DATA;     
  assign rx_sop_n[i]                                 = FLRX[i].SOP_N;    
  assign rx_eop_n[i]                                 = FLRX[i].EOP_N;    
  assign rx_sof_n[i]                                 = FLRX[i].SOF_N;    
  assign rx_eof_n[i]                                 = FLRX[i].EOF_N;    
  assign rx_rem[(i+1)*RXDREMWIDTH-1:RXDREMWIDTH*i]   = FLRX[i].DREM;     
  assign rx_src_rdy_n[i]                             = FLRX[i].SRC_RDY_N;
  assign FLRX[i].DST_RDY_N                           = rx_dst_rdy_n[i];
  end
endgenerate

// -------------------- Module body -------------------------------------------
dma_module_wrapper

   VHDL_DUT_U  (
    // Common Interface
     .CLK            (CLK),
     .RESET          (RESET),
    
    // Misc signals 
     
    
    // Read interface (FrameLinks)
     .TX_DATA        (tx_data),
     .TX_SOF_N       (tx_sof_n),
     .TX_SOP_N       (tx_sop_n),
     .TX_EOP_N       (tx_eop_n),
     .TX_EOF_N       (tx_eof_n),
     .TX_REM         (tx_rem),
     .TX_SRC_RDY_N   (tx_src_rdy_n),
     .TX_DST_RDY_N   (tx_dst_rdy_n),
     
    // Read interface (FrameLinks)
     .RX_DATA        (rx_data),
     .RX_SOF_N       (rx_sof_n),
     .RX_SOP_N       (rx_sop_n),
     .RX_EOP_N       (rx_eop_n),
     .RX_EOF_N       (rx_eof_n),
     .RX_REM         (rx_rem),
     .RX_SRC_RDY_N   (rx_src_rdy_n),
     .RX_DST_RDY_N   (rx_dst_rdy_n),
        
    // Upstream InternalBus
     .UP_DATA        (IBUP.DATA),
     .UP_SOP_N       (IBUP.SOP_N),
     .UP_EOP_N       (IBUP.EOP_N),
     .UP_SRC_RDY_N   (IBUP.SRC_RDY_N),
     .UP_DST_RDY_N   (IBUP.DST_RDY_N), 
     
    // Downstream InternalBus
     .DOWN_DATA      (IBDOWN.DATA),
     .DOWN_SOP_N     (IBDOWN.SOP_N),
     .DOWN_EOP_N     (IBDOWN.EOP_N),
     .DOWN_SRC_RDY_N (IBDOWN.SRC_RDY_N),
     .DOWN_DST_RDY_N (IBDOWN.DST_RDY_N),

     .RX_INTERRUPT   (RX_INTERRUPT),
     .TX_INTERRUPT   (TX_INTERRUPT)
);


endmodule : DUT
