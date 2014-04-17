/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU
 * File Name:    sv_alu_ga_pkg.sv
 * Description:  Genetic Algorithm Components Package.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         13.2.2014
 * ************************************************************************** */

 package sv_alu_ga_pkg; 
  
   // Package imports
   import sv_alu_seq_pkg::*;     
   import sv_alu_param_pkg::*;
   import sv_alu_env_pkg::*;
   import sv_alu_coverage_pkg::*;
   
   // Includes
   `include "alu_chromosome.svh"
   `include "alu_chromosome_array.svh"
   //`include "chromosome_sequencer.svh"
   `include "alu_ga_input_transaction.svh"
   `include "transaction_ga_sequencer.svh"
   `include "alu_ga_agent.svh"
    
 endpackage : sv_alu_ga_pkg
