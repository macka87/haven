/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    sv_fl_pkg
 * Description:  SystemVerilog FrameLink Components
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */

// FrameLink interface
`include "fl_ifc.sv"

package sv_fl_pkg; 
  import sv_basic_comp_pkg::*;   // Import SV basic classes
  import sv_types_pkg::*;        // Import package of user defined types 

  //`include "fl_assertion_checker.sv"
  `include "fl_transaction.sv"
  `include "fl_driver.sv"
  `include "fl_sender.sv"
  `include "fl_gen_input_controller.sv"
  `include "fl_output_controller.sv"
  `include "fl_gen_output_controller.sv"
  `include "fl_assertion_reporter.sv"
  `include "fl_signal_reporter.sv"
  `include "fl_responder.sv"
  `include "fl_responder_simple.sv"
  `include "fl_monitor.sv"
  `include "fl_command_coverage.sv"
endpackage : sv_fl_pkg
