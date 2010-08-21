/*
 * testbench.sv: Top Entity for OBUF automatic test
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
 * $Id: testbench.sv 13466 2010-04-09 07:28:07Z xsanta06 $
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
  logic            XGMII_CLK   = 0;
  logic            MI32_CLK    = 0;
  logic            FL_CLK      = 0;
  logic            RESET;
  iXgmiiSdrTx      XGMII   (XGMII_CLK, RESET);
//  iLinkState       LINK    (CLK, RESET);
  iMi32            MI32    (MI32_CLK, RESET);
  iFrameLinkRx #(FL_WIDTH_RX, FL_REM_WIDTH_RX) FL (FL_CLK, RESET);

  
  //-- Clock generation -------------------------------------------------------
  always #(XGMII_CLK_PERIOD/2)   XGMII_CLK = ~XGMII_CLK;
  always #(MI32_CLK_PERIOD/2)    MI32_CLK = ~MI32_CLK;
  always #(FL_CLK_PERIOD/2)      FL_CLK = ~FL_CLK;


  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.RESET        (RESET),
               .XGMII_CLK    (XGMII_CLK),
               .MI32_CLK     (MI32_CLK),
               .FL_CLK       (FL_CLK),
               .XGMII        (XGMII),
//               .LINK         (LINK),
               .MI32         (MI32),
               .FL           (FL)
              );


  //-- Test -------------------------------------------------------------------
  TEST TEST_U (.RESET        (RESET),
               .XGMII_CLK    (XGMII_CLK),
               .MI32_CLK     (MI32_CLK),
               .FL_CLK       (FL_CLK),
               .XGMII        (XGMII),
//               .LINK         (LINK),
               .MI32         (MI32),
               .FL           (FL)
              );

endmodule : testbench
