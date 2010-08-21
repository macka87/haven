/*
 * testbench.sv: Top Entity for IB_SWITCH automatic test
 * Copyright (C) 2008 CESNET
 * Author(s): Tomas Malek <tomalek@liberouter.org>
 *            Petr Kobiersky <kobiersky@liberouter.org>
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
 * $Id: testbench.sv 1217 2008-02-07 21:48:08Z tomalek $
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
  logic CLK   = 0;
  logic RESET;
  iIB   PORT0_DOWN  (CLK, RESET);
  iIB   PORT0_UP    (CLK, RESET);
  iIB   PORT1_DOWN  (CLK, RESET);
  iIB   PORT1_UP    (CLK, RESET);
  iIB   PORT2_DOWN  (CLK, RESET);
  iIB   PORT2_UP    (CLK, RESET);
  
  //-- Clock generation -------------------------------------------------------
  always #(cClkPeriod/2) CLK = ~CLK;

  //-- Unit Under Test --------------------------------------------------------
  IB_SWITCH_SV UUT      (.CLK          (CLK),
                         .RESET        (RESET),
                         .PORT0_DOWN   (PORT0_DOWN),
                         .PORT0_UP     (PORT0_UP),
                         .PORT1_DOWN   (PORT1_DOWN),
                         .PORT1_UP     (PORT1_UP),
                         .PORT2_DOWN   (PORT2_DOWN),
                         .PORT2_UP     (PORT2_UP)          
                        );

  //-- Test -------------------------------------------------------------------
  TEST TEST_U          (.CLK          (CLK),
                        .RESET        (RESET),
                        .PORT0_DOWN   (PORT0_DOWN),
                        .PORT0_UP     (PORT0_UP),
                        .PORT1_DOWN   (PORT1_DOWN),
                        .PORT1_UP     (PORT1_UP),
                        .PORT2_DOWN   (PORT2_DOWN),
                        .PORT2_UP     (PORT2_UP)          
                       );
endmodule : testbench



