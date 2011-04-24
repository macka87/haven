/* *****************************************************************************
 * Project Name: HGEN Functional Verification
 * File Name:    testbench.sv - testbench file
 * Description:  Connection of the DUT to the verification environment. 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */
 

import test_pkg::*; // Test constants

module testbench;

  // -- Testbench wires and interfaces ----------------------------------------
  logic            CLK   = 0;
  logic            RESET;
  iFrameLinkRx #(DATA_WIDTH, DREM_WIDTH) RX  (CLK, RESET);
  iFrameLinkTx #(DATA_WIDTH, DREM_WIDTH) TX  (CLK, RESET);
  iFrameLinkTx #(DATA_WIDTH, DREM_WIDTH) MONITOR  (CLK, RESET);
  iMi32                                  MI32_RXTX (CLK, RESET);

  //-- Clock generation -------------------------------------------------------
  always #(CLK_PERIOD/2) CLK = ~CLK;

  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.CLK       (CLK),
               .RESET     (RESET),
               .RX        (RX),
               .TX        (TX),
               .MONITOR   (TX),
	             .MI32_RXTX (MI32_RXTX)
              );

  //-- Test cases -------------------------------------------------------------
  TEST TEST_U (.CLK          (CLK),
               .RESET        (RESET),
               .RX           (RX),
               .TX           (TX),
               .MONITOR      (TX),
	             .MI32_RXTX    (MI32_RXTX)
              );
endmodule : testbench
