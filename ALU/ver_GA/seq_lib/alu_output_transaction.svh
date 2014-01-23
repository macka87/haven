/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU
 * File Name:    alu_output_transaction.svh
 * Description:  Output Transaction Class for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         23.1.2014
 * ************************************************************************** */

/*!
 * \brief Output ALU Transaction
 * 
 * This class represents transaction which contains values of input signals for
 * the DUT.
 */
 
 class AluOutputTransaction;

  /*! 
   * Data Members
   */
   
   logic [DATA_WIDTH-1:0] ex_alu;  // included data
   
  /*!
   * Methods
   */ 
  
   // Standard UVM methods
   extern function void print(string name);
   extern function AluOutputTransaction clone(AluOutputTransaction rhs = null);
   extern function bit compare(AluOutputTransaction rhs);
   
 endclass: AluOutputTransaction
 
 
 
/*! 
 * Implementation of the clone function.
 */
 function AluOutputTransaction AluOutputTransaction::clone(AluOutputTransaction rhs = null);
   
   AluOutputTransaction alu_trans;
   
   if (rhs == null)
     alu_trans = new();
   else 
     $cast(alu_trans, rhs);
   
   alu_trans.ex_alu = ex_alu;
   
   return alu_trans;
 endfunction: clone  



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
 function bit AluOutputTransaction::compare(AluOutputTransaction rhs);
   AluOutputTransaction alu_trans;
   bit same = 1;
   
   if(!$cast(alu_trans, rhs)) begin
     $write("do_compare:", "$cast failed!");
     return 0;
   end
   
   if (ex_alu != alu_trans.ex_alu) 
     begin
       same = 0;
       $write("ALU_OUTPUT does not match!\n");
       $write("EXPECTED TRANSACTION: %d\n", ex_alu);
       $write("\n");
     end
   
   return same;
 endfunction: compare