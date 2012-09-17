/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    sv_basic_comp_pkg.sv
 * Description:  SystemVerilog OVM Basic Verification Components
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         17.9.2012
 * ************************************************************************** */
 
package sv_basic_comp_pkg; 
   import sv_types_pkg::*; // Import package of user defined types 

  `include "basic_driver.sv"
  `include "basic_input_controller.sv"
  `include "basic_monitor.sv"
  `include "basic_output_controller.sv"
  `include "basic_sequencer.sv"
  `include "basic_transaction.sv"    
  `include "basic_transaction_table.sv"
endpackage : sv_basic_comp_pkg