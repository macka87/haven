/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    haven_input_transaction.sv
 * Description:  OVM HAVEN Input Transaction Class 
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz>, 
 *               Michaela Belesova <xbeles00@stud.fit.vutbr.cz>
 * Date:         27.9.2012
 * ************************************************************************** */

/*!
 * \brief Basic HAVEN Input Transaction
 * 
 * This class represents abstract input transaction which contains specific 
 * number of parts: HAVEN Transaction = x HAVEN sequence items. 
 */
 
 class HavenInputTransaction extends ovm_sequence_item;

   // registration of component 
   `ovm_object_utils(HavenInputTransaction)
   
  /*! 
   * Constructor
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
       $fatal("HAVEN Input Transaction: Task send must be implemented in derived              class"); 
   endtask : send   
   
 endclass: HavenInputTransaction