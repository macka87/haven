/* *****************************************************************************
 * Project Name: ALU Functional Verification
 * File Name:    dut.sv - Design Under Test
 * Description:  DUT interfaces
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         22.3.2012 
 * ************************************************************************** */

import test_pkg::*; // Test constants
  
/*
 *  Module declaration
 */
 
 module DUT (
   input logic    CLK,
  // input logic    RST,
   iAluIn.aluin   ALU_IN,
   iAluOut.aluout ALU_OUT
 );

/*
 *  Module body
 */
 ALU_ENT #(
     .DATA_WIDTH    (DATA_WIDTH)       
   )

   VHDL_DUT_U (
     .CLK            (CLK),
     .RST            (ALU_IN.RST),
	   .ACT            (ALU_IN.ACT),
     
     // Input interface
     .OP             (ALU_IN.OP),
     .ALU_RDY        (ALU_IN.ALU_RDY),
     .MOVI           (ALU_IN.MOVI),
     .REG_A          (ALU_IN.REG_A),
     .REG_B          (ALU_IN.REG_B),
     .MEM            (ALU_IN.MEM),
     .IMM            (ALU_IN.IMM),
     
     // Output interface
     .EX_ALU         (ALU_OUT.EX_ALU),
     .EX_ALU_VLD     (ALU_OUT.EX_ALU_VLD)
   );

 endmodule : DUT
