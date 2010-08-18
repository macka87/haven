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
 * $Id: dut.sv 12330 2009-12-24 01:07:54Z xsanta06 $
 *
 * TODO:
 *
 */
 
// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module DUT (
   input logic               RESET,
   input logic               XGMII_CLK,
   output logic              SAU_CLK,
   output logic              PCD_CLK,
   input logic               MI32_CLK,
   input logic               FL_CLK,
   iXgmiiSdrRx.dut           XGMII,
   iSamplingUnit.dut         SAU,
   iPacodag.dut              PCD,
//   iLinkState.dut            LINK,
   iMi32.dut                 MI32,
   iFrameLinkTx.dut          FL
);

// -------------------- Module body -------------------------------------------
ibuf_xgmii_sdr_pcd_norec#(
      .DFIFO_SIZE      (DFIFO_SIZE    ),
      .HFIFO_SIZE      (HFIFO_SIZE    ),
      .HFIFO_MEMTYPE   (HFIFO_MEMTYPE ),
      .CTRL_HDR_EN     (CTRL_HDR_EN   ),
      .CTRL_FTR_EN     (CTRL_FTR_EN   ),
      .MACS            (MACS          ),
      .INBANDFCS       (INBANDFCS     ),
      .CNT_ERROR_SIZE  (CNT_ERROR_SIZE),
      .FL_WIDTH_TX     (FL_WIDTH_TX   ),
      .FL_RELAY        (FL_RELAY      )
   )

   VHDL_DUT_U  (
    // Common Interface
     .RESET          (RESET),
    
    // XGMII interface 
     .RXCLK          (XGMII_CLK),
     .RXD            (XGMII.RXD),
     .RXC            (XGMII.RXC),

    // SAU interface 
     .SAU_CLK        (SAU_CLK),
     .SAU_REQ        (SAU.REQ),
     .SAU_ACCEPT     (SAU.ACCEPT),
     .SAU_DV         (SAU.DV),

    // PACODAG interface
     .CTRL_CLK       (PCD_CLK      ),
     .CTRL_DATA      (PCD.DATA     ),
     .CTRL_REM       (PCD.REM      ),
     .CTRL_SOP_N     (PCD.SOP_N    ),
     .CTRL_EOP_N     (PCD.EOP_N    ),
     .CTRL_SRC_RDY_N (PCD.SRC_RDY_N),
     .CTRL_DST_RDY_N (PCD.DST_RDY_N),
     .CTRL_SOP       (PCD.SOP      ),
     .CTRL_RDY       (PCD.RDY      ),

    // Statistic data interface 
//     .STAT           (PCD.STAT   ),
     .STAT_DV        (PCD.STAT_DV),

    // Link state interface 
//     .LINK_UP        (LINK.LINK_UP      ),
//     .INCOMING_PCKT  (LINK.INCOMING_PCKT),

    // FrameLink interface
     .FL_CLK         (FL_CLK),
     .TX_DATA        (FL.DATA),
     .TX_SOF_N       (FL.SOF_N),
     .TX_SOP_N       (FL.SOP_N),
     .TX_EOP_N       (FL.EOP_N),
     .TX_EOF_N       (FL.EOF_N),
     .TX_REM         (FL.DREM),
     .TX_SRC_RDY_N   (FL.SRC_RDY_N),
     .TX_DST_RDY_N   (FL.DST_RDY_N),

    // MI32 interface
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
