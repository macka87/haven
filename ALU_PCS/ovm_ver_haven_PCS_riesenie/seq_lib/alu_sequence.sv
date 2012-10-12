/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_sequence.sv
 * Description:  OVM Sequence of Transactions for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         27.9.2012
 * ************************************************************************** */

/*!
 * \brief AluSequence
 * 
 * This class represents OVM sequence of random input transactions for ALU.
 */
 
 class AluSequence extends ovm_sequence #(AluInputTransaction);

   // registration of component tools
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
      
       assert($cast(req, create_item(AluInputTransaction::get_type(), m_sequencer, "req")));
 
       start_item(req);
       assert(req.randomize());
       //req.display();
       finish_item(req);
        
     end
     
   endtask: body

 endclass: AluSequence