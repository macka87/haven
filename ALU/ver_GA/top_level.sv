/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU
 * File Name:    top_level.sv
 * Description:  The Top Module of Verification Environment for ALU.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         21.1.2014 
 * ************************************************************************** */

/*!
 * \brief TOP LEVEL module
 * 
 * The topmost encapsulation level of the verification environment.
 */

 module Top_TB;

   import sv_alu_test_pkg::*;   
   import sv_alu_param_pkg::*;
  
   logic pokus;
  
   //! clock and reset signals
   logic CLK;                           
   logic RST;    
  
   //! SystemVerilog virtual interfaces for DUT                      
   iAluIn  dut_alu_in_if   (CLK, RST);  // ALU input interface
   iAluOut dut_alu_out_if  (CLK, RST);  // ALU output interface
   
   //! Normal test
   AluTest   alu_test;
   AluGATest alu_ga_test;
   AluRSTest alu_rs_test;
  
   //! DUT 
   ALU_ENT #(
     .DATA_WIDTH    (DATA_WIDTH)       
   )

   VHDL_DUT_U (
     .CLK            (CLK),
     .RST            (RST),
	   .ACT            (dut_alu_in_if.ACT),
     
     // Input interface
     .OP             (dut_alu_in_if.OP),
     .ALU_RDY        (dut_alu_in_if.ALU_RDY),
     .MOVI           (dut_alu_in_if.MOVI),
     .REG_A          (dut_alu_in_if.REG_A),
     .REG_B          (dut_alu_in_if.REG_B),
     .MEM            (dut_alu_in_if.MEM),
     .IMM            (dut_alu_in_if.IMM),
     
     // Output interface
     .EX_ALU         (dut_alu_out_if.EX_ALU),
     .EX_ALU_VLD     (dut_alu_out_if.EX_ALU_VLD)
   );
   
   
   
   //! TEST
   initial begin
     alu_test = new(dut_alu_in_if, dut_alu_out_if);
     alu_ga_test = new(dut_alu_in_if, dut_alu_out_if);
     alu_rs_test = new(dut_alu_in_if, dut_alu_out_if);
     
     if (VERSION == 0) alu_test.run();
     else if (VERSION == 1)  alu_ga_test.run(); 
     else if (VERSION == 2)  alu_rs_test.run(); 
 
     $stop;	
   end

   
  
   //! Clock and Reset initial blocks
   // Clock generation
   initial begin
     CLK = 0;
     forever begin
       #(CLK_PERIOD/2) CLK = ~CLK;
     end
   end
   
   

   // Reset at the start of the simulation
   initial begin
     RST = 1;
     #(RESET_TIME);
     RST = 0;
   end 
  
 endmodule: Top_TB
