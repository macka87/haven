/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    sv_alu_ga_pkg.sv
 * Description:  UVM Genetic Algorithm Components Package.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         2.8.2013
 * ************************************************************************** */

 package sv_alu_ga_pkg; 
  
   // Standard UVM import & include
   import uvm_pkg::*;
   `include "uvm_macros.svh"
  
   // Package imports
   import sv_basic_ga_pkg::*;
   import sv_alu_seq_pkg::*;
   import sv_alu_coverage_pkg::*;
  
   // Includes
   `include "alu_chromosome.svh"
   `include "chromosome_array.svh"
   `include "chromosome_sequence_config.svh"
   `include "chromosome_sequence.svh" 
   `include "alu_ga_input_transaction.svh"
   `include "alu_ga_transaction_sequence_config.svh"
   `include "alu_ga_transaction_sequence.svh"
   
 endpackage : sv_alu_ga_pkg
