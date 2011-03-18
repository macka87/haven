/* *****************************************************************************
 * Project Name: NetCOPE Adder Functional Verification
 * File Name:    sv_netcope_adder_pkg.sv 
 * Description:  Components of the Verification Environment
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */
 
/*
 * FrameLink Interface
 */  
 
package sv_netcope_adder_pkg; 

  import sv_basic_comp_pkg::*; // Import SV basic verification components 
  import sv_fl_pkg::*;         // Import SV FrameLink classes
  
  `include "scoreboard.sv"

endpackage : sv_netcope_adder_pkg
