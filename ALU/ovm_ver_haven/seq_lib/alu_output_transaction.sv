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
   bit ex_alu_vld;
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
      $write("EX_ALU_VLD: %d\n", ex_alu_vld);   
      $write("EX_ALU: %d\n", ex_alu);
      $write("\n");
   endfunction: display

  /*!
   * Copies the current value of the object instance to the specified object
   * instance. Returns a reference to the target instance.
   * 
   * \param to - original transaction        
   */
   virtual function AluOutputTransaction copy(HavenOutputTransaction to = null);
   
     AluOutputTransaction tr;
     if (to == null)
       tr = new();
     else 
       $cast(tr, to);

     tr.ex_alu_vld = ex_alu_vld;
     tr.ex_alu     = ex_alu;
             
     copy = tr;
   endfunction : copy
   
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
   virtual function bit compare(input HavenOutputTransaction to, 
                                output string diff, input int kind = -1);
     bit same = 1; // Suppose that are same
     AluOutputTransaction tr;
     $cast(tr, to);
       
     if (ex_alu_vld != tr.ex_alu_vld) 
     begin
       same = 0;
       $write(diff, "EX_ALU_VLD does not match!\n");
     end
     
     if (ex_alu != tr.ex_alu) 
     begin
       same = 0;
       $write(diff, "EX_ALU does not match!\n");
     end
     
     compare = same; 
   endfunction : compare 
   
 endclass: AluOutputTransaction
