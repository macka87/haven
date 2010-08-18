/*
 * testbench.sv: Top Entity for FL_DISCARD_STAT automatic test
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
 * $Id: testbench.sv 14629 2010-07-23 11:32:04Z pus $
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
  iFrameLinkRx #(DRIVER0_DATA_WIDTH, DRIVER0_DREM_WIDTH)   
                                               RX_DRIV [CHANNELS] (CLK, RESET);
  iFrameLinkTx #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) 
                                               TX_MUX  [CHANNELS] (CLK, RESET);
  iFrameLinkRx #(DRIVER0_DATA_WIDTH, DRIVER0_DREM_WIDTH)   
                                               RX_DEMUX[CHANNELS] (CLK, RESET);
  iFrameLinkTx #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) 
                                               TX_MON  [CHANNELS] (CLK, RESET);
  iFrameLinkRx #(DRIVER0_DATA_WIDTH, DRIVER0_DREM_WIDTH)   RX (CLK, RESET);
  iFrameLinkTx #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) TX (CLK, RESET);
  iMi32                                  MI (CLK, RESET);
  iDiscardStat #(CHANNELS, STATUS_WIDTH) DS (CLK, RESET);

  
  //-- Clock generation -------------------------------------------------------
  always #(CLK_PERIOD/2) CLK = ~CLK;

  //-- Set TX DST_RDY_N always to 0 (active)
  generate
    for (genvar i=0; i<CHANNELS; i++) begin
      always @(posedge CLK) TX_MON[i].DST_RDY_N <= RESET;
    end
  endgenerate

  //-- Multiplexor and demultiplexor connection -------------------------------
  generate
    for (genvar i=0; i<CHANNELS; i++) begin
      assign TX_MUX[i].DATA       = RX_DRIV[i].DATA;
      assign TX_MUX[i].DREM       = RX_DRIV[i].DREM;
      assign TX_MUX[i].SOF_N      = RX_DRIV[i].SOF_N;
      assign TX_MUX[i].EOF_N      = RX_DRIV[i].EOF_N;
      assign TX_MUX[i].SOP_N      = RX_DRIV[i].SOP_N;
      assign TX_MUX[i].EOP_N      = RX_DRIV[i].EOP_N;
      assign TX_MUX[i].SRC_RDY_N  = RX_DRIV[i].SRC_RDY_N;
      assign RX_DRIV[i].DST_RDY_N = TX_MUX[i].DST_RDY_N;

      assign TX_MON[i].DATA       = RX_DEMUX[i].DATA;
      assign TX_MON[i].DREM       = RX_DEMUX[i].DREM;
      assign TX_MON[i].SOF_N      = RX_DEMUX[i].SOF_N;
      assign TX_MON[i].EOF_N      = RX_DEMUX[i].EOF_N;
      assign TX_MON[i].SOP_N      = RX_DEMUX[i].SOP_N;
      assign TX_MON[i].EOP_N      = RX_DEMUX[i].EOP_N;
      assign TX_MON[i].SRC_RDY_N  = RX_DEMUX[i].SRC_RDY_N;
      assign RX_DEMUX[i].DST_RDY_N = TX_MON[i].DST_RDY_N;
    end
  endgenerate


  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.CLK     (CLK),
               .RESET   (RESET),
               .RX      (RX),
               .TX      (TX),
               .MI      (MI),
               .DS      (DS)
              );


  //-- Test -------------------------------------------------------------------
  TEST TEST_U (.CLK          (CLK),
               .RESET        (RESET),
               .RX_DRIV      (RX_DRIV),
               .TX_MUX       (TX_MUX),
               .RX_DEMUX     (RX_DEMUX),
               .TX_MON       (TX_MON),
               .RX           (RX),
               .TX           (TX),
               .MI           (MI),
               .RX_CHAN      (DS),
               .TX_CHAN      (DS),
               .STAT         (DS)
              );

endmodule : testbench
