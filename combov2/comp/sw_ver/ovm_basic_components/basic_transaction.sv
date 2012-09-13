/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    basic_transaction.sv
 * Description:  OVM Basic Transaction Class
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         16.8.2012
 * ************************************************************************** */

 `include "ovm_macros.svh"

 package BasicTransaction_pkg;
  
   //include official ovm package
   import ovm_pkg::*;
 
  /*!
   * \brief BasicTransaction
   * 
   * This class is parent class for any transaction.
   */
   class BasicTransaction extends ovm_sequence_item;

     //zaregistrovanie sekvencie
     `ovm_object_utils(BasicTransaction)

    /*! 
     * Constructor - creates BasicTransaction object  
     *
     * \param name     - transaction instance name
     */  
     function new (string name = "");
       super.new(name);
     endfunction: new
   
    /*!
     * Function displays the current value of the transaction or data described
     * by this instance in a human-readable format on the standard output.
     *
     * \param prefix - transaction type
     */
     virtual function void display(string prefix = "");
     endfunction : display
  
    /*!
     * Copies the current value of the object instance to the specified object
     * instance. Returns a reference to the target instance.
     * 
     * \param to - original transaction        
     */
     virtual function BasicTransaction copy(BasicTransaction to = null);
       return null;
     endfunction : copy

    /*!
     * Writes transactions to external file.
     */
     virtual function void fwrite (int fileDescr);
     endfunction : fwrite  
    
    /*!
     * Reads transactions from external file.
     */
     virtual function void fread (int fileDescr);
     endfunction : fread
   
    /*!
     * Compares the current value of the object instance with the current value
     * of the specified object instance, according to the specified kind. 
     * Returns TRUE (i.e., non-zero) if the value is identical. If the value is
     * different, FALSE is returned and a descriptive text of the first 
     * difference found is returned in the specified string variable. The kind 
     * argument may be used to implement different comparison functions (e.g., 
     * full compare, comparison of rand properties only, comparison of all 
     * properties physically implemented in a protocol and so on.)
     * 
     * \param to - transaction instance
     * \param diff - first difference
     * \param kind - comparation function                 
     */
     virtual function bit compare(input BasicTransaction to, 
                                  output string diff, input int kind = -1);
       return 1'b0;
     endfunction : compare     
   
   endclass : BasicTransaction
 
 endpackage: BasicTransaction_pkg