                                                                        /* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    haven_sequence_item.sv
 * Description:  OVM HAVEN Sequence Item Class 
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz>, 
 *               Michaela Belesova <xbeles00@stud.fit.vutbr.cz>
 * Date:         26.9.2012
 * ************************************************************************** */

/*!
 * \brief Basic HAVEN Sequence Item 
 * 
 * This class represents one part of HAVEN transaction:
 * HAVEN Transaction = x HAVEN sequence items. 
 */
 
 class HavenSequenceItem extends ovm_sequence_item;

   // registration of component 
   `ovm_object_utils(HavenSequenceItem)
   
  /*! 
   * Constructor 
   *
   * \param name - instance name
   */
   function new (string name = "");
     super.new(name);
   endfunction: new

  /*!
   * Virtual task send - transaction is sent to the connected component. 
   */
   virtual task getRaw();
     assert (0) 
       $fatal("HAVEN Sequence Item: Task getRaw() must be implemented in derived     class"); 
   endtask : getRaw   
   
 endclass: HavenSequenceItem