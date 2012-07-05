/* *****************************************************************************
 * Project Name: FIFO Functional Verification
 * File Name:    sv_fl_fifo_pkg.sv 
 * Description:  Components of the Verification Environment
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */
 
/*
 * FrameLink Interface
 */  

// FrameLink FIFO Control Interface
`include "fl_fifo_ifc.sv"
 
package sv_fl_fifo_pkg; 

  import sv_basic_comp_pkg::*; // Import SV basic verification components 
  import sv_types_pkg::*;      // Import package of user defined types
  import sv_fl_pkg::*;         // Import SV FrameLink classes
   
  `include "fl_fifo_ctrl_checker.sv"
  `include "scoreboard.sv"

endpackage : sv_fl_fifo_pkg
