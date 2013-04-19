/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    top_level.sv
 * Description:  The UVM Top Module of Verification Environment for ALU.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

/*!
 * \brief TOP LEVEL module
 * 
 * The topmost encapsulation level of the verification environment.
 */

 module Top_TB;

   import uvm_pkg::*;
  
   import sv_alu_env_pkg::*;
   import sv_alu_test_pkg::*;   
   import sv_alu_param_pkg::*;
  
   //! clock and reset signals
   logic CLK;                           
   logic RST;    
  
   //! SystemVerilog virtual interfaces for DUT                      
   iAluIn  dut_alu_in_if   (CLK, RST);  // ALU input interface
   iAluOut dut_alu_out_if  (CLK, RST);  // ALU output interface
  
   //! DUT 
   ALU_ENT #(
     .DATA_WIDTH    (DATA_WIDTH)       
   )

   VHDL_DUT_U (
     .CLK            (CLK),
     .RST            (dut_alu_in_if.RST),
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
  
   //! UVM initial block
   initial begin
     // virtual interface wrapping
     uvm_config_db #(virtual iAluIn)::set(null, "uvm_test_top", "AluIn_vif", dut_alu_in_if);
     uvm_config_db #(virtual iAluOut)::set(null, "uvm_test_top", "AluOut_vif", dut_alu_out_if);

     // start running of the test 
     run_test();
     $finish;
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