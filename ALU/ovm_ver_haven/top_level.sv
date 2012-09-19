/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    top_level.sv
 * Description:  OVM Top Module of Verification Enviroment for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         18.9.2012
 * ************************************************************************** */

import test_pkg::*; 
import sv_alu_pkg::*;

/*!
 * \brief AluTop
 * 
 * The topmost encapsulation level of the verification
 */

module AluTop;

  // DUT primary interfaces
  logic CLK;                                      // Clock signal
  iAluIn  #(DATA_WIDTH) dut_alu_in_if   (CLK);    // ALU input interface
  iAluOut #(DATA_WIDTH) dut_alu_out_if  (CLK);    // ALU output interface
  
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
      dut_alu_in_if.RST = 1;
    end
  
  initial
    begin: blk

      // DUT Interface Wrapper
      AluDutIfWrapper #(DATA_WIDTH) if_wrapper = new("if_wrapper", dut_alu_in_if, dut_alu_out_if);
      
      // Registration of DUT Interface Wrapper in configuration table
      // Arguments: path(* = all objects can use it), name, value, don't clone
      set_config_object("*", "AluDutIfWrapper", if_wrapper, 0);
      
      // Start of the simulation
      run_test("AluTest");
      
    end

endmodule: AluTop