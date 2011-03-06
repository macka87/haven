/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    dut.sv - Design Under Test
 * Description:  DUT interfaces.
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */
  
import test_pkg::*; // Test constants

/*
 *  Module declaration
 */
 
 module DUT (
   input logic CLK,
   input logic RESET
 );

/*
 *  Module body
 */
 
 ENTITY_NAME #(
   )

   VHDL_DUT_U (
     .CLK               (CLK),
     .RESET             (RESET)
   );

endmodule : DUT
