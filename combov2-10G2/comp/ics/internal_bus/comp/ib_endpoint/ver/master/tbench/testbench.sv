/*
 * testbench.sv: Top Entity for IB_ENDPOINT automatic test
 * Copyright (C) 2007 CESNET
 * Author(s): Viktor Pus <pus@liberouter.org>
 *            Petr Kobiersky <kobiersky@liberouter.org>
 *            Tomas Malek <tomalek@liberouter.org>
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
 * $Id: testbench.sv 333 2007-09-05 20:07:59Z xkobie00 $
 *
 * TODO:
 *
 */

import test_pkg::*; // Test constants and types

// ----------------------------------------------------------------------------
//                                 TESTBENCH
// ----------------------------------------------------------------------------
module testbench;

  // -- Testbench wires and registers -----------------------------------------
  logic CLK = 0;
  logic RESET;
  iIbEndpointWrite64 WR   (CLK, RESET);
  iIbEndpointRead64s RD   (CLK, RESET);
  iIbEndpointMaster  BM   (CLK, RESET);
  iInternalBusLink   UP   (CLK, RESET);
  iInternalBusLink   DOWN (CLK, RESET);

  //-- Clock generation -------------------------------------------------------
  always #(cClkPeriod/2) CLK = ~CLK;

  //-- Unit Under Test --------------------------------------------------------
  IB_ENDPOINT_MASTER UUT ( // Unit Under Test
      .CLK     (CLK),
      .RESET   (RESET),
      .WR      (WR),
      .RD      (RD),
      .BM      (BM),
      .IB_UP   (UP),
      .IB_DOWN (DOWN));

  //-- Test -------------------------------------------------------------------
  TEST TEST_U ( // Testing program
      .CLK     (CLK),
      .RESET   (RESET),
      .WR      (WR),
      .RD      (RD),
      .BM      (BM),
      .IB_UP   (UP),
      .IB_DOWN (DOWN));

endmodule : testbench
