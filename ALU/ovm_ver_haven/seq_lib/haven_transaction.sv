/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    haven_transaction.sv
 * Description:  OVM HAVEN Transaction Class 
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz>, 
 *               Michaela Belesova <xbeles00@stud.fit.vutbr.cz>
 * Date:         20.9.2012
 * ************************************************************************** */

/*!
 * \brief Basic HAVEN Transaction
 * 
 * This class represents abstract transaction which contains determine number of 
 * parts: HAVEN Transaction = x HAVEN sequence items. 
 */
 
 class HavenTransaction extends ovm_sequence_item;

   // registration of component 
   `ovm_object_utils(HavenTransaction)
   
  /*! 
   * Constructor - creates AluTransaction object  
   *
   * \param name - transaction instance name
   */
   function new (string name = "");
     super.new(name);
   endfunction: new

  /*!
   * Virtual task send - transaction is sent to the connected component. 
   */
   virtual task send();
     assert (0) 
       $fatal("HAVEN Transaction: Task send must be implemented in derived 
               class"); 
   endtask : send   
   
 endclass: HavenTransaction