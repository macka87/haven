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
 * $Id: dut.sv 13945 2010-06-04 13:39:17Z xvikto03 $
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
   input logic               CLK,
   iXgmiiSdrRx.dut           XGMII_RX[XGMII_COUNT],
   iXgmiiSdrTx.dut           XGMII_TX[XGMII_COUNT],
   iMi32.dut                 MI32
);

wire [(XGMII_COUNT * 64) - 1 : 0] xgmii_rxd;
wire [(XGMII_COUNT * 8) - 1 : 0] xgmii_rxc;
wire [(XGMII_COUNT * 64) - 1 : 0] xgmii_txd;
wire [(XGMII_COUNT * 8) - 1 : 0] xgmii_txc;

generate
    for(genvar i = 0; i < XGMII_COUNT; ++i) begin
        assign xgmii_rxd[(i + 1) * 64 - 1 : i * 64] = XGMII_RX[i].RXD;
        assign xgmii_rxc[(i + 1) * 8 - 1 : i * 8] = XGMII_RX[i].RXC;
        assign XGMII_TX[i].TXD = xgmii_txd[(i + 1) * 64 - 1 : i * 64];
        assign XGMII_TX[i].TXC = xgmii_txc[(i + 1) * 8 - 1 : i * 8];
    end;
endgenerate;

// -------------------- Module body -------------------------------------------
xgmii_crossbar_top#(
      .XGMII_COUNT     (XGMII_COUNT)
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK            (CLK),
     .RESET          (RESET),
    
    // XGMII interface 
     .XGMII_RXD            (xgmii_rxd),
     .XGMII_RXC            (xgmii_rxc),
     .XGMII_TXD            (xgmii_txd),
     .XGMII_TXC            (xgmii_txc),

    // MI32 interface
     .DWR         (MI32.DWR ),
     .ADDR        (MI32.ADDR),
     .RD          (MI32.RD  ),
     .WR          (MI32.WR  ),
     .BE          (MI32.BE  ),
     .DRD         (MI32.DRD ),
     .ARDY        (MI32.ARDY),
     .DRDY        (MI32.DRDY)
);


endmodule : DUT
