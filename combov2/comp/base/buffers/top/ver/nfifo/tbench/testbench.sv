/*
 * testbench.sv: Top Entity for automatic test
 * Copyright (C) 2008 CESNET
 * Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
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
 * $Id: testbench.sv 7267 2009-02-26 14:51:11Z xsanta06 $
 *
 * TODO:
 *
 */
 

// ----------------------------------------------------------------------------
//                                 TESTBENCH
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module testbench;
   
  // -- Testbench wires and registers -----------------------------------------
  logic            CLK   = 0;
  logic            RESET;
  
  // input interface
  iNFifoTx #(DATA_WIDTH, FLOWS, BLOCK_SIZE, LUT_MEMORY, GLOB_STATE) FW (CLK, RESET);
  // output interface
  iNFifoRx #(DATA_WIDTH, FLOWS, BLOCK_SIZE, LUT_MEMORY, GLOB_STATE) FR (CLK, RESET);
  
    
  //-- Clock generation -------------------------------------------------------
  always #(CLK_PERIOD/2) CLK = ~CLK;

  //-- Unit Under Test --------------------------------------------------------
  DUT DUT_U           (.CLK          (CLK),
                       .RESET        (RESET),
                       .FW           (FW),
                       .FR           (FR)
                      );

  //-- Test -------------------------------------------------------------------
  TEST TEST_U         (.CLK          (CLK),
                       .RESET        (RESET),
                       .FW           (FW),
                       .FR           (FR),
                       .MONITOR      (FR)
                       );
endmodule : testbench
