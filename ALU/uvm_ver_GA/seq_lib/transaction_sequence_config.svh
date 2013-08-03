/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    transaction_sequence_config.svh
 * Description:  Configuration object for Transaction Sequence.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.6.2013
 * ************************************************************************** */

/*!
 * \brief TransactionSequenceConfig
 * 
 * This class represents the configuration object for Transaction Sequence.
 */
 
 class TransactionSequenceConfig extends uvm_object;
    
   //! UVM Factory Registration Macro
   `uvm_object_utils(TransactionSequenceConfig)
   
  /*! 
   * Data Members
   */  
   
   // TRANSACTION PARAMETERS
   int trans_count     = 10;
          
  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "TransactionSequenceConfig");
   
 endclass: TransactionSequenceConfig
 
 
 
/*! 
 * Constructor - creates the TransactionSequenceConfig object  
 */
 function TransactionSequenceConfig::new(string name = "TransactionSequenceConfig");
   super.new(name);
 endfunction: new 