/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    transaction_sequencer.sv
 * Description:  UVM Sequencer Class for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.6.2013
 * ************************************************************************** */

/*! 
 * Constructor - creates the TransactionSequencer object  
 */
 function TransactionSequencer::new(string name = "TransactionSequencer", uvm_component parent = null);
   super.new(name, parent);
 endfunction: new