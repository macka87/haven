/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    top_level.sv
 * Description:  OVM Top Module of Verification Enviroment for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         18.9.2012
 * ************************************************************************** */

/*!
 * \brief AluTop
 * 
 * The topmost encapsulation level of the verification
 */

module AluTop;

  import ovm_pkg::*;
  import sv_alu_env_pkg::*;
  import sv_alu_test_pkg::*;   
  import sv_alu_param_pkg::*;
      
  // DUT primary interfaces
  logic CLK;                           // Clock signal
  logic RST;                           // Reset signal
  iAluIn  dut_alu_in_if   (CLK, RST);  // ALU input interface
  iAluOut dut_alu_out_if  (CLK, RST);  // ALU output interface
  
  // DUT 
  AluDUT dut ( CLK, dut_alu_in_if, dut_alu_out_if);

  // Clock generation
  initial
    begin
      CLK = 0;
      forever begin
        #(CLK_PERIOD/2) CLK = ~CLK;
      end
    end

  // Reset at the start of the simulation
  initial
    begin
      RST = 1;
      #(RESET_TIME);
      RST = 0;
      #(200*RESET_TIME);
      RST = 1;
      #(RESET_TIME);
      RST = 0;
    end 
  
  initial
    begin: blk

      // DUT Interface Wrapper
      AluDutIfWrapper if_wrapper = new("if_wrapper", dut_alu_in_if, dut_alu_out_if);
      
      // Registration of DUT Interface Wrapper in configuration table
      // Arguments: path(* = all objects can use it), name, value, don't clone
      set_config_object("*", "AluDutIfWrapper", if_wrapper, 0);
      
      // Start of the simulation
      run_test("AluTest");
      
    end

endmodule: AluTop