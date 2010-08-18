/*
 * DUT.sv: Design under test
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
 * $Id: dut.sv 14904 2010-08-06 10:47:46Z xspinl00 $
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
   output logic              RX_INTERRUPT,
   output logic              TX_INTERRUPT,
   iInternalBusUp.ib_up      IBUP,
   iInternalBusDown.ib_down  IBDOWN,
   iFrameLinkRx.dut          FLRX,
   iFrameLinkTx.dut          FLTX[TX_IFC_COUNT],
   iMi32.dut                 MI,
   iDiscardStat.dut          DS
);

// Signals for DUT conection
// FrameLink Interface
wire [TXDWIDTH*TX_IFC_COUNT-1:0] tx_data;  
wire [TX_IFC_COUNT-1:0]      tx_sop_n;
wire [TX_IFC_COUNT-1:0]      tx_eop_n;
wire [TX_IFC_COUNT-1:0]      tx_sof_n;
wire [TX_IFC_COUNT-1:0]      tx_eof_n;
wire [TXDREMWIDTH*TX_IFC_COUNT-1:0] tx_rem;
wire [TX_IFC_COUNT-1:0]      tx_src_rdy_n;
wire [TX_IFC_COUNT-1:0]      tx_dst_rdy_n;

// Connecting FR to interfaces
generate
for (genvar i=0; i<TX_IFC_COUNT; i++) begin  
  assign FLTX[i].DATA      = tx_data[(i+1)*TXDWIDTH-1:TXDWIDTH*i];
  assign FLTX[i].SOP_N     = tx_sop_n[i];
  assign FLTX[i].EOP_N     = tx_eop_n[i];
  assign FLTX[i].SOF_N     = tx_sof_n[i];
  assign FLTX[i].EOF_N     = tx_eof_n[i];
  assign FLTX[i].DREM      = tx_rem[(i+1)*TXDREMWIDTH-1:TXDREMWIDTH*i];
  assign FLTX[i].SRC_RDY_N = tx_src_rdy_n[i];
  assign tx_dst_rdy_n[i]   = FLTX[i].DST_RDY_N;
  end
endgenerate

// -------------------- Module body -------------------------------------------
dma_module_gen#(
     .RX_IFC_COUNT              (RX_IFC_COUNT),
     .TX_IFC_COUNT              (TX_IFC_COUNT),
     .RX_BUFFER_SIZE            (RX_BUFFER_SIZE),
     .TX_BUFFER_SIZE            (TX_BUFFER_SIZE),
     .RX_FL_WIDTH               (RX_FL_WIDTH),
     .TX_FL_WIDTH               (TX_FL_WIDTH),

     .RX_DISCARD_EN             (RX_DISCARD_EN),
     .DESC_BASE_ADDR            (DESC_BASE_ADDR),
     .DESC_BLOCK_SIZE           (DESC_BLOCK_SIZE)
     )

   VHDL_DUT_U  (
    // Common Interface
     .CLK            (CLK),
     .RESET          (RESET),
    
    // Misc signals 
     .RX_INTERRUPT     (RX_INTERRUPT),
     .TX_INTERRUPT     (TX_INTERRUPT),
     .RX_BUFFER_STATUS (DS.BUF_STATUS),
    
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
     .RX_DATA        (FLRX.DATA),
     .RX_SOF_N       (FLRX.SOF_N),
     .RX_SOP_N       (FLRX.SOP_N),
     .RX_EOP_N       (FLRX.EOP_N),
     .RX_EOF_N       (FLRX.EOF_N),
     .RX_REM         (FLRX.DREM),
     .RX_SRC_RDY_N   (FLRX.SRC_RDY_N),
     .RX_DST_RDY_N   (DS.DST_RDY_N),
     .RX_ADDR        (DS.RX_CHAN),
        
    // Upstream InternalBus
     .UP_DATA        (IBUP.DATA),
     .UP_SOF_N       (IBUP.SOP_N),
     .UP_EOF_N       (IBUP.EOP_N),
     .UP_SRC_RDY_N   (IBUP.SRC_RDY_N),
     .UP_DST_RDY_N   (IBUP.DST_RDY_N), 
     
    // Downstream InternalBus
     .DOWN_DATA      (IBDOWN.DATA),
     .DOWN_SOF_N     (IBDOWN.SOP_N),
     .DOWN_EOF_N     (IBDOWN.EOP_N),
     .DOWN_SRC_RDY_N (IBDOWN.SRC_RDY_N),
     .DOWN_DST_RDY_N (IBDOWN.DST_RDY_N),

    // MI32
     .MI32_DWR         (MI.DWR),
     .MI32_ADDR        (MI.ADDR),
     .MI32_BE          (MI.BE),
     .MI32_RD          (MI.RD),
     .MI32_WR          (MI.WR),
     .MI32_DRDY        (MI.DRDY),
     .MI32_ARDY        (MI.ARDY),
     .MI32_DRD         (MI.DRD) 

);


endmodule : DUT
