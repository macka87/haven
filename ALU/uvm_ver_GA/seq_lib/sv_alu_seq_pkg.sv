/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    sv_alu_seq_pkg.sv
 * Description:  UVM ALU Sequence Package
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

 package sv_alu_seq_pkg;

   // Standard UVM import & include
   import uvm_pkg::*;
   `include "uvm_macros.svh"
  
   // Package imports
   import sv_alu_param_pkg::*; 
         
   // Includes
   `include "alu_input_transaction.svh"
   `include "transaction_sequence_config.svh" 
   `include "transaction_sequence.svh"
   `include "transaction_sequencer.svh"
   `include "alu_output_transaction.svh"
 endpackage