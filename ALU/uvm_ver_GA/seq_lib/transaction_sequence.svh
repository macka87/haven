/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    transaction_sequence.svh
 * Description:  UVM Sequence for ALU Transactions 
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.6.2013
 * ************************************************************************** */

/*!
 * \brief TransactionSequence
 * 
 * This class represents UVM sequence of random input transactions for ALU.
 */
 
 class TransactionSequence extends uvm_sequence #(AluInputTransaction);

   //! UVM Factory Registration Macro
   `uvm_object_utils(TransactionSequence)
  
  /*! 
   * Data Members
   */ 
   
   int trans_count;
   TransactionSequenceConfig transaction_sequence_cfg; 
   
  /*! 
   * Component Members
   */ 
   Population pop_sequencer;
   

  /*!
   * Methods
   */
  
   // Standard UVM methods
   extern function new(string name = "TransactionSequence");
   extern task body();  
   extern task post_body();   
   
   // Own UVM methods
   extern task configureSequence(TransactionSequenceConfig transaction_sequence_cfg);
   extern task configureTrans(AluChromosome alu_chr, AluGAInputTransaction alu_in_trans);
      
 endclass: TransactionSequence