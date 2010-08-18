/*
 * testbench.sv: Top Entity for DMA Module Generic automatic test
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
 * $Id: testbench.sv 14541 2010-07-21 07:15:35Z xsanta06 $
 *
 * TODO:
 *
 */
 

// ----------------------------------------------------------------------------
//                                 TESTBENCH
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module testbench;

  // -- Testbench wires and interfaces ----------------------------------------
  logic            CLK   = 0;
  logic            RESET;
  logic            RX_INTERRUPT;
  logic            TX_INTERRUPT;
  iInternalBusUp   #(IBWIDTH)            IBUP    (CLK, RESET);
  iInternalBusDown #(IBWIDTH)            IBDOWN  (CLK, RESET);
  iFrameLinkRx #(RXDWIDTH, RXDREMWIDTH)  RX_DRIV [RX_IFC_COUNT] (CLK, RESET);
  iFrameLinkTx #(RXDWIDTH, RXDREMWIDTH)  TX_MUX  [RX_IFC_COUNT] (CLK, RESET);
  iFrameLinkRx #(RXDWIDTH, RXDREMWIDTH)  FLRX    (CLK, RESET);
  iFrameLinkTx #(TXDWIDTH, TXDREMWIDTH)  FLTX    [TX_IFC_COUNT] (CLK, RESET);
  iMi32                                  MI      (CLK, RESET);
  iDiscardStat #(RX_IFC_COUNT, STATUSWIDTH) DS   (CLK, RESET);

  
  //-- Clock generation -------------------------------------------------------
  always #(CLK_PERIOD/2) CLK = ~CLK;

  //-- Multiplexor connection -------------------------------------------------
  generate
    for (genvar i=0; i<RX_IFC_COUNT; i++) begin
      assign TX_MUX[i].DATA       = RX_DRIV[i].DATA;
      assign TX_MUX[i].DREM       = RX_DRIV[i].DREM;
      assign TX_MUX[i].SOF_N      = RX_DRIV[i].SOF_N;
      assign TX_MUX[i].EOF_N      = RX_DRIV[i].EOF_N;
      assign TX_MUX[i].SOP_N      = RX_DRIV[i].SOP_N;
      assign TX_MUX[i].EOP_N      = RX_DRIV[i].EOP_N;
      assign TX_MUX[i].SRC_RDY_N  = RX_DRIV[i].SRC_RDY_N;
      assign RX_DRIV[i].DST_RDY_N = TX_MUX[i].DST_RDY_N;
    end
  endgenerate


  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.CLK     (CLK),
               .RESET   (RESET),
               .RX_INTERRUPT (RX_INTERRUPT),
               .TX_INTERRUPT (TX_INTERRUPT),
               .IBUP    (IBUP),
               .IBDOWN  (IBDOWN),
               .FLRX    (FLRX),
               .FLTX    (FLTX),
               .MI      (MI),
               .DS      (DS)
              );


  //-- Test -------------------------------------------------------------------
  TEST TEST_U (.CLK     (CLK),
               .RESET   (RESET),
               .RX_INTERRUPT (RX_INTERRUPT),
               .TX_INTERRUPT (TX_INTERRUPT),
               .IBUP    (IBUP),
               .IBDOWN  (IBDOWN),
               .RX_DRIV (RX_DRIV),
               .TX_MUX  (TX_MUX),
               .FLRX    (FLRX),
               .FLTX    (FLTX),
               .MONITOR (FLTX),
               .MI      (MI),
               .DS      (DS),
               .STAT    (DS)
              );

endmodule : testbench
