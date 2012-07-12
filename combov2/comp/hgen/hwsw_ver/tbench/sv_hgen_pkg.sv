/* *****************************************************************************
 * Project Name: HGEN Functional Verification
 * File Name:    sv_hgen_pkg.sv 
 * Description:  Components of the Verification Environment
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         24.4.2011 
 * ************************************************************************** */
 
/*
 * FrameLink Interface
 */  

package sv_hgen_pkg; 

  import sv_basic_comp_pkg::*; // Import SV basic verification components 
  import sv_types_pkg::*;      // Import package of user defined types
  import sv_fl_pkg::*;         // Import SV FrameLink classes
  
  `include "scoreboard.sv"

endpackage : sv_hgen_pkg
