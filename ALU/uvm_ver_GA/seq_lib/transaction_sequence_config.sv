/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    transaction_sequence_config.sv
 * Description:  Configuration object for Transaction Sequence.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.6.2013
 * ************************************************************************** */

/*! 
 * Constructor - creates the TransactionSequenceConfig object  
 */
 function TransactionSequenceConfig::new(string name = "TransactionSequenceConfig");
   super.new(name);
 endfunction: new