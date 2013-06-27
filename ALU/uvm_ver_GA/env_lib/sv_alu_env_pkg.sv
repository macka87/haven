/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    sv_alu_env_pkg.sv
 * Description:  UVM ALU Verification Environment Package.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

 package sv_alu_env_pkg;

   // Standard UVM import & include
   import uvm_pkg::*;
   `include "uvm_macros.svh"
  
   // Package imports
   import sv_alu_param_pkg::*;
   import sv_alu_seq_pkg::*;
   import math_pkg::*;

   // Includes
   `include "alu_agent_config.svh"
   `include "alu_agent_config.sv"
   `include "alu_env_config.svh"
   `include "alu_env_config.sv"
   `include "alu_driver.svh"
   `include "alu_driver.sv"
   `include "alu_agent.svh"
   `include "alu_agent.sv"
   `include "alu_env.svh"
   `include "alu_env.sv"
     
   /*`include "alu_dut_if_wrapper.sv"
   `include "alu_driver.sv"
   `include "alu_monitor.sv"
   `include "alu_input_subscriber.sv"
   `include "alu_output_subscriber.sv"
   `include "alu_scoreboard.sv" 
   `include "alu_env.sv"*/ 

 endpackage