/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    transaction_sequence.svh
 * Description:  UVM Sequence for ALU Transactions 
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         3.8.2013
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
   * Methods
   */
  
   // Standard UVM methods
   extern function new(string name = "TransactionSequence");
   extern task body();  
   
   // Own UVM methods
   extern task configureSequence(TransactionSequenceConfig transaction_sequence_cfg);
         
 endclass: TransactionSequence
 
 
 
/*! 
 * Constructor - creates TransactionSequence object  
 */
 function TransactionSequence::new(string name = "TransactionSequence");
   super.new(name);
 endfunction: new   



/*! 
 * Body - implements behavior of the transaction
 */ 
 task TransactionSequence::body;
   AluInputTransaction   alu_in_trans, alu_in_trans_c;
   int cnt = 0;
        
   // check configuration for Transaction Sequence
   if (!uvm_config_db #(TransactionSequenceConfig)::get(null, get_full_name(), "TransactionSequenceConfig", transaction_sequence_cfg)) 
     `uvm_error("BODY", "TransactionSequenceConfig doesn't exist!"); 
   
   // configure Sequence of Transactions 
   configureSequence(transaction_sequence_cfg); 
     
   alu_in_trans = AluInputTransaction::type_id::create();
     
   while (cnt < trans_count) begin
     assert($cast(alu_in_trans_c, alu_in_trans.clone)); 
     start_item(alu_in_trans_c);
     assert(alu_in_trans_c.randomize());
     //alu_in_trans_c.print("TRANS_SEQUENCE: ALU TRANSACTION");
     finish_item(alu_in_trans_c);
     cnt++; 
   end 
   
 endtask: body



 /*! 
 * configureSequence - configure Sequence with data from the configuration object
 */ 
 task TransactionSequence::configureSequence(TransactionSequenceConfig transaction_sequence_cfg);
   trans_count = transaction_sequence_cfg.trans_count;
 endtask: configureSequence