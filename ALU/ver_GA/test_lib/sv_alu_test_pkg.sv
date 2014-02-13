/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    sv_alu_test_pkg.sv
 * Description:  UVM ALU Test Package
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

 `include "alu_dut_if.sv"

 package sv_alu_test_pkg;
   
   // Package imports
   import sv_alu_param_pkg::*;
   import sv_alu_ga_pkg::*;
   import sv_alu_coverage_pkg::*;
   import sv_alu_env_pkg::*;
  
   // Includes  
   `include "alu_ga_test.svh"
   `include "alu_test.svh"
     
 endpackage