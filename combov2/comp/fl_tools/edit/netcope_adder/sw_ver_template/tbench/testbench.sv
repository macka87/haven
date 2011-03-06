/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
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
    
  //-- Clock generation -------------------------------------------------------
  always #(CLK_PERIOD/2) CLK = ~CLK;

  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.CLK     (CLK),
               .RESET   (RESET)
              );

  //-- Test cases -------------------------------------------------------------
  TEST TEST_U (.CLK     (CLK),
               .RESET   (RESET)
              );

endmodule : testbench
