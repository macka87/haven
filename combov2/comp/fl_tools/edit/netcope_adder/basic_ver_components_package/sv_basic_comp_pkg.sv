/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    sv_basic_comp_pkg.sv
 * Description:  SystemVerilog Basic Verification Components 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */

package sv_basic_comp_pkg; 
  `include "transaction.sv"
  `include "netcope_transaction.sv"
  `include "generator.sv"
  `include "input_cbs.sv"
  `include "input_controller.sv"
  `include "gen_input_controller.sv"    
  `include "driver.sv"
  `include "sender.sv"
  `include "input_wrapper.sv"
  `include "output_cbs.sv"
  `include "monitor.sv"
  `include "transaction_table.sv"
  `include "lfsr.sv"
endpackage : sv_basic_comp_pkg
