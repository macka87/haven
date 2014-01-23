/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU
 * File Name:    sv_alu_seq_pkg.sv
 * Description:  ALU Sequence Package
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         21.1.2014
 * ************************************************************************** */

 package sv_alu_seq_pkg;

   // Package imports
   import sv_alu_param_pkg::*; 
         
   // Includes
   `include "alu_input_transaction.svh"
   `include "transaction_sequencer.svh"
   /*`include "alu_output_transaction.svh"*/
 endpackage