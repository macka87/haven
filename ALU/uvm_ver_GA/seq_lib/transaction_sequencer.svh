/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    transaction_sequencer.svh
 * Description:  UVM Sequencer Class for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.6.2013
 * ************************************************************************** */

/*!
 * \brief TransactionSequencer
 * 
 * This class manages random inputs for DUT and sends them to driver.
 */

 class TransactionSequencer extends uvm_sequencer #(AluInputTransaction);
    
   //! UVM Factory Registration Macro
   `uvm_component_utils(TransactionSequencer)

  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "TransactionSequencer", uvm_component parent = null);

 endclass: TransactionSequencer
 
 
 
/*! 
 * Constructor - creates the TransactionSequencer object  
 */
 function TransactionSequencer::new(string name = "TransactionSequencer", uvm_component parent = null);
   super.new(name, parent);
 endfunction: new 