/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU
 * File Name:    transaction_sequencer.svh
 * Description:  Sequencer Class for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         21.1.2014
 * ************************************************************************** */

/*!
 * \brief TransactionSequencer
 * 
 * This class manages random inputs for DUT and sends them to driver.
 */

 class TransactionSequencer;
    
  /*! 
   * Data Members
   */ 
  
  /*! 
   * Channels
   */    
   mailbox #(AluInputTransaction) inputMbx; 
   
  /*!
   * Methods
   */
  
   // User-defined methods
   extern task run();

 endclass: TransactionSequencer


 
/*! 
 * Generate transactions
 */ 
 task TransactionSequencer::run();
   AluInputTransaction alu_in_trans, alu_in_trans_c;
   int cnt = 0;
   
   //$write("\n\n########## TRANSACTION SEQUENCER ##########\n\n");
   
   alu_in_trans = new();
   
   //while (cnt < TRANS_COUNT) begin
   forever begin
     alu_in_trans_c = alu_in_trans.clone();               
     
     assert(alu_in_trans_c.randomize());
     //alu_in_trans_c.print("TRANS_SEQUENCE: ALU TRANSACTION");
     inputMbx.put(alu_in_trans_c);
     cnt++; 
   end 
 endtask: run 
 
