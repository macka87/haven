/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_ga_transaction_sequence_config.svh
 * Description:  Configuration object for ALU Transaction Sequence.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         3.8.2013
 * ************************************************************************** */

/*!
 * \brief AluGATransactionSequenceConfig
 * 
 * This class represents the configuration object for ALU Transaction Sequence.
 */
 
 class AluGATransactionSequenceConfig extends TransactionSequenceConfig;
    
   //! UVM Factory Registration Macro
   `uvm_object_utils(AluGATransactionSequenceConfig)
   
  /*! 
   * Data Members
   */  
   
   // TRANSACTION PARAMETERS
   int populationSize  = 10;   // Size of a population
       
  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "AluGATransactionSequenceConfig");
   
 endclass: AluGATransactionSequenceConfig
 
 
 
/*! 
 * Constructor - creates the AluGATransactionSequenceConfig object  
 */
 function AluGATransactionSequenceConfig::new(string name = "AluGATransactionSequenceConfig");
   super.new(name);
 endfunction: new 