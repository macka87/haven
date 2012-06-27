/* *****************************************************************************
 * Project Name: ALU Functional Verification
 * File Name:    sv_alu_pkg.sv 
 * Description:  Components of the Verification Environment
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         22.3.2012 
 * ************************************************************************** */
 
/*
 * ALU Interfaces
 */  

`include "alu_ifc.sv"
 
package sv_alu_pkg; 

  import sv_basic_comp_pkg::*; // Import SV basic verification components 
  import ga_pkg::*;            // Import genetic algorithm verification components 
  
  `include "alu_input_transaction.sv"
  `include "alu_ga_input_transaction.sv"
  `include "alu_chromosome.sv"
  //`include "alu_lfsr_generator.sv"
  `include "alu_output_transaction.sv"
  `include "alu_sender.sv"
  `include "alu_driver.sv"
  `include "alu_gen_input_controller.sv"
  `include "alu_ga_input_controller.sv"
  `include "alu_output_controller.sv"
  `include "alu_monitor.sv"
  `include "scoreboard.sv"
  `include "alu_coverage.sv"

endpackage : sv_alu_pkg
