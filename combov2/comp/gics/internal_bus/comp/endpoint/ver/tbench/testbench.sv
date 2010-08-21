/*
 * testbench.sv: ib_endpoint verification testbench
 * Copyright (C) 2008 CESNET
 * Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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
 * $Id: testbench.sv 8956 2009-06-24 21:16:49Z washek $
 *
 * TODO:
 *
 */

import ib_params_pkg::*;
import params::*;

module testbench;
  
  // -- Testbench wires and interfaces ----------------------------------------
  logic CLK;
  logic RESET;
  iInternalBusRx       #(G.DATA_WIDTH)               IB_DOWN  (CLK, RESET);
  iInternalBusTx       #(G.DATA_WIDTH)               IB_UP    (CLK, RESET);
  iIbEndpointWrite     #(G.DATA_WIDTH, G.ADDR_WIDTH) WR       (CLK, RESET);
  iIbEndpointRead      #(G.DATA_WIDTH, G.ADDR_WIDTH) RD       (CLK, RESET);
  iInternalBusRx       #(G.DATA_WIDTH)               BM       (CLK, RESET);
  iIbEndpointBMDone                                  BM_DONE  (CLK, RESET);
  
  //-- Clock generation -------------------------------------------------------
  always begin
    CLK = 1;
    #(CLK_PERIOD/2);
    CLK = 0;
    #(CLK_PERIOD-CLK_PERIOD/2);
  end

  //-- Verification environment -----------------------------------------------
  TEST TEST_U (
    .CLK     (CLK),
    .RESET   (RESET),
    .WR      (WR),
    .RD      (RD),
    .IB_DOWN (IB_DOWN),
    .IB_UP   (IB_UP),
    .BM      (BM),
    .BM_DONE (BM_DONE)
  );
  
  //-- Design Under Test ------------------------------------------------------
  if (MI_TEST == 0) begin
    IB_ENDPOINT_SV #(G) DUT (
      .CLK     (CLK),
      .RESET   (RESET),
      .WR      (WR),
      .RD      (RD),
      .IB_DOWN (IB_DOWN),
      .IB_UP   (IB_UP),
      .BM      (BM),
      .BM_DONE (BM_DONE)
    );
  end else begin
    IB_ENDPOINT_MI_SV #(G) DUT (
      .CLK     (CLK),
      .RESET   (RESET),
      .WR      (WR),
      .RD      (RD),
      .IB_DOWN (IB_DOWN),
      .IB_UP   (IB_UP),
      .BM      (BM),
      .BM_DONE (BM_DONE)
    );
  end
  
endmodule : testbench
