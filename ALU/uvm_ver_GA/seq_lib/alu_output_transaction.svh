/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_output_transaction.svh
 * Description:  UVM Output Transaction Class for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         9.7.2013
 * ************************************************************************** */

/*!
 * \brief Output ALU Transaction
 * 
 * This class represents transaction which contains values of input signals for
 * the DUT.
 */
 
 class AluOutputTransaction extends uvm_sequence_item;

   //! UVM Factory Registration Macro
   `uvm_object_utils(AluOutputTransaction)
   
  /*! 
   * Data Members
   */
   
   // included data
   logic [DATA_WIDTH-1:0] ex_alu;
   
  /*!
   * Methods
   */ 
  
   // Standard UVM methods
   extern function new(string name = "AluOutputTransaction");
   extern function void print(string name);
   extern function void do_copy(uvm_object rhs);
   extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);   
   
 endclass: AluOutputTransaction
 
 
 
/*! 
 * Constructor - creates AluOutputTransaction object  
 */
 function AluOutputTransaction::new(string name = "AluOutputTransaction");
   super.new(name);
 endfunction: new



/*! 
 * Implementation of the do_copy() virtual function.
 */
 function void AluOutputTransaction::do_copy(uvm_object rhs);
   AluOutputTransaction alu_trans;
   
   if(!$cast(alu_trans, rhs)) begin
     uvm_report_error("do_copy:", "$cast failed!");
     return;
   end
   
   super.do_copy(rhs);
   
   ex_alu = alu_trans.ex_alu;
 endfunction: do_copy  



/*! 
 * Print - displays ALU Input Transaction content  
 */    
 function void AluOutputTransaction::print(string name);
   if (name != "") begin
     $write("---------------------------------------------------------\n");
     $write("-- %s\n",name);
     $write("---------------------------------------------------------\n");
   end
      
   $write("EX_ALU: %b\n", ex_alu);
   $write("\n");
 endfunction: print



/*! 
 * Implementation of the do_compare() virtual function.
 */
 function bit AluOutputTransaction::do_compare(uvm_object rhs, uvm_comparer comparer);
   AluOutputTransaction alu_trans;
   
   if(!$cast(alu_trans, rhs)) begin
     uvm_report_error("do_compare:", "$cast failed!");
     return 0;
   end
   
   return(super.do_compare(rhs, comparer) && (ex_alu == alu_trans.ex_alu));
 endfunction: do_compare