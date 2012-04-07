/* *****************************************************************************
 * Project Name: ALU Functional Verification
 * File Name:    testbench.sv - testbench file
 * Description:  Connection of the DUT to the verification environment. 
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         22.3.2012 
 * ************************************************************************** */

import test_pkg::*; // Test constants

module testbench;

  // -- Testbench wires and interfaces ----------------------------------------
  logic                  CLK   = 0;
  logic                  RST;
  iAluIn  #(DATA_WIDTH)  ALU_IN  (CLK, RESET);
  iAluOut #(DATA_WIDTH)  ALU_OUT (CLK, RESET);
      
  //-- Clock generation -------------------------------------------------------
  always #(CLK_PERIOD/2) CLK = ~CLK;
  
  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.CLK     (CLK),
               .RST     (RST),
               .ALU_IN  (ALU_IN),
               .ALU_OUT (ALU_OUT)
              );

  //-- Test cases -------------------------------------------------------------
  TEST TEST_U (.CLK     (CLK),
               .RST     (RST),
               .ALU_IN  (ALU_IN),
               .ALU_OUT (ALU_OUT)
              );

endmodule : testbench
