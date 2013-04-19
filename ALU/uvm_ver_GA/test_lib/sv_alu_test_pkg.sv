/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    sv_alu_test_pkg.sv
 * Description:  UVM ALU Test Package
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

 package sv_alu_test_pkg;
   
   // Standard UVM import & include
   import uvm_pkg::*;
   `include "uvm_macros.svh"
   
   // Package imports
   import sv_alu_param_pkg::*;
   import sv_alu_seq_pkg::*;
   import sv_alu_env_pkg::*;
  
   // Includes  !! svh !!
   //`include "alu_test.sv"

 endpackage