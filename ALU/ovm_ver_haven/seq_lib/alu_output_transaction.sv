/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_output_transaction.sv
 * Description:  OVM Output Transaction Class for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         27.9.2012
 * ************************************************************************** */

/*!
 * \brief AluOutputTransaction
 * 
 * This class represents transaction which contains values of output signals for
 * the DUT.
 */
 
 class AluOutputTransaction extends HavenOutputTransaction;

   // registration of component tools
   `ovm_object_utils(AluOutputTransaction)
   
   //included data
   logic [DATA_WIDTH-1:0] ex_alu;

  /*! 
   * Constructor
   *
   * \param name     - instance name
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
   function void display(string prefix = "");
      if (prefix != "")
      begin
        $write("---------------------------------------------------------\n");
        $write("-- %s\n",prefix);
        $write("---------------------------------------------------------\n");
      end

      $write("EX_ALU: %b\n", ex_alu);
      $write("\n");
   endfunction: display

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
   virtual function bit compare(input AluOutputTransaction tr);
     string msg;
     bit same = 1; // Suppose that are same
            
     if (ex_alu !== tr.ex_alu) 
     begin
       same = 0;
       $sformat(msg, "EX_ALU does not match!\n");
       ovm_report_error("OUTPUT TRANSACTION", msg, OVM_NONE);
     end
     
     compare = same; 
   endfunction : compare 
   
 endclass: AluOutputTransaction
