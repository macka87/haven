/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_top.sv
 * Description:  OVM Top Module of Verification Enviroment for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         10.9.2012
 * ************************************************************************** */

/*!
 * \brief AluTop
 * 
 * The topmost encapsulation level of the verification
 */

module AluTop;

  import alu_general_settings_pkg::*;
  import alu_dut_if_wrapper_pkg::*;
  import alu_test_pkg::*;
  
  AluDutIf #(pDataWidth) dut_if1 ();
  AluDut dut1 ( ._if(dut_if1) );

  //clock generation
  initial
    begin
      dut_if1.CLK = 0;
      forever begin
        #(CLK_PERIOD/2) dut_if1.CLK = ~dut_if1.CLK;
      end
    end

  //reset at the begining of the simulation
  initial
    begin
      dut_if1.RST = 1;
    end
  
  initial
    begin: blk

      //creating wrapper for the virtual interface so as it can be placed into 
      //the configuration table
      //we need virtual interface in the configuration table taht other objects
      //can use it
      AluDutIfWrapper #(pDataWidth) if_wrapper = new("if_wrapper", dut_if1);
      
      //puts wrapper into the configuration table
      //arguments: path(* = all objects can use it), name, value, don't clone
      set_config_object("*", "AluDutIfWrapper", if_wrapper, 0);
      
      //runs simulation
      run_test("AluTest");
      
    end

endmodule: AluTop