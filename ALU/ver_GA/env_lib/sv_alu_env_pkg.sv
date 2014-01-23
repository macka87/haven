/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU 
 * File Name:    sv_alu_env_pkg.sv
 * Description:  ALU Verification Environment Package.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         21.1.2014 
 * ************************************************************************** */

 `include "alu_dut_if.sv"

 package sv_alu_env_pkg;

   // Package imports
   import sv_alu_seq_pkg::*;
   //import sv_alu_ga_pkg::*;
   import sv_alu_param_pkg::*;
   import math_pkg::*;
     
   // Includes
   `include "alu_driver.svh"
   `include "alu_monitor.svh"
   `include "alu_scoreboard.svh"
   `include "alu_agent.svh"
        
 endpackage