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
 * $Id: dut.sv 13466 2010-04-09 07:28:07Z xsanta06 $
 *
 * TODO:
 *
 */
 
// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module DUT (
   input logic         RESET,
   input logic         XGMII_CLK,
   input logic         MI32_CLK,
   input logic         FL_CLK,
   iXgmiiSdrTx.dut     XGMII,
//   iLinkState.dut      LINK,
   iMi32.dut           MI32,
   iFrameLinkRx.dut    FL
);

// -------------------- Module body -------------------------------------------
obuf_xgmii_sdr_norec#(
      .DFIFO_SIZE      (DFIFO_SIZE   ),
      .HFIFO_SIZE      (HFIFO_SIZE   ),
      .HFIFO_MEMTYPE   (HFIFO_MEMTYPE),
      .CTRL_CMD        (CTRL_CMD     ),
      .FL_WIDTH_RX     (FL_WIDTH_RX  )
   )

   VHDL_DUT_U  (
    
    // XGMII interface 
     .RESET_XGMII    (RESET),
     .CLK_INT        (XGMII_CLK),
     .XGMII_SDR_TXD  (XGMII.TXD),
     .XGMII_SDR_TXC  (XGMII.TXC),

    // Link state interface 
//     .OUTGOING_PCKT  (LINK.OUTGOING_PCKT),

    // FrameLink interface
     .RESET_FL       (RESET),
     .FL_CLK         (FL_CLK),
     .RX_DATA        (FL.DATA),
     .RX_SOF_N       (FL.SOF_N),
     .RX_SOP_N       (FL.SOP_N),
     .RX_EOP_N       (FL.EOP_N),
     .RX_EOF_N       (FL.EOF_N),
     .RX_REM         (FL.DREM),
     .RX_SRC_RDY_N   (FL.SRC_RDY_N),
     .RX_DST_RDY_N   (FL.DST_RDY_N),

    // MI32 interface
     .RESET_MI       (RESET),
     .MI_CLK         (MI32_CLK ),
     .MI_DWR         (MI32.DWR ),
     .MI_ADDR        (MI32.ADDR),
     .MI_RD          (MI32.RD  ),
     .MI_WR          (MI32.WR  ),
     .MI_BE          (MI32.BE  ),
     .MI_DRD         (MI32.DRD ),
     .MI_ARDY        (MI32.ARDY),
     .MI_DRDY        (MI32.DRDY)
      
);

endmodule : DUT
