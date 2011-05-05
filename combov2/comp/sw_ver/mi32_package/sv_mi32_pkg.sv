/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    sv_mi32_pkg
 * Description:  SystemVerilog MI32 Components
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */

// MI32 Interface
`include "mi32_ifc.sv"

package sv_mi32_pkg; 

  import sv_basic_comp_pkg::*;        // Import SV basic classes

  `include "mi32_transaction.sv"
  `include "mi32_driver.sv"
  `include "mi32_monitor.sv"
  `include "mi32_input_controller.sv"

endpackage : sv_mi32_pkg
