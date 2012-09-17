/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_sequence.sv
 * Description:  OVM Sequence of Transactions for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         11.9.2012
 * ************************************************************************** */

`include "ovm_macros.svh"
package alu_sequence_pkg;
 import ovm_pkg::*;
 import alu_transaction_result_pkg::*; 
 
/*!
 * \brief AluSequence
 * 
 * This class is OVM sequence of random input transactions for ALU.
 */
 
 class AluSequence #(int pDataWidth = 8) extends ovm_sequence #(AluTransaction);

   //registration of component tools
   `ovm_object_utils(AluSequence)

  /*! 
   * Constructor - creates AluSequence object  
   *
   * \param name     - instance name
   */
   function new (string name = "");
     super.new(name);
   endfunction: new

  /*! 
   * Body - implements behavior of the transaction
   */ 
   task body;
     
     forever
     begin
      
       AluTransaction #(pDataWidth) tx;
       tx = AluTransaction::type_id::create("tx");
 
       start_item(tx);
       assert( tx.randomize() );
       //tx.display();
       finish_item(tx);
        
     end
     
   endtask: body

 endclass: AluSequence
 
endpackage: alu_sequence_pkg 