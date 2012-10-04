/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    haven_output_transaction.sv
 * Description:  OVM HAVEN Output Transaction Class 
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz>, 
 *               Michaela Belesova <xbeles00@stud.fit.vutbr.cz>
 * Date:         27.9.2012
 * ************************************************************************** */

/*!
 * \brief Basic HAVEN Output Transaction
 * 
 * This class represents abstract output transaction which contains specific
 * number of parts: HAVEN Transaction = x HAVEN sequence items. 
 */
 
 class HavenOutputTransaction extends ovm_sequence_item;

   // registration of component 
   `ovm_object_utils(HavenOutputTransaction)
   
  /*! 
   * Constructor
   *
   * \param name - transaction instance name
   */
   function new (string name = "");
     super.new(name);
   endfunction: new

  /*!
   * Virtual task receive - transaction is received from the connected
   * component. 
   */
   virtual task receive();
     string msg;
     
     assert (0) begin 
       $sformat(msg, "Task receive must be implemented in derived class!\n");
       ovm_report_fatal("HAVEN OUTPUT TRANSACTION", msg, OVM_NONE);
     end  
   endtask : receive   
   
 endclass: HavenOutputTransaction