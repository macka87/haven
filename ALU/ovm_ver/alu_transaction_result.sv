/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_transaction_result.sv
 * Description:  OVM Transaction Class for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         12.9.2012
 * ************************************************************************** */

/*!
 * \brief BasicTransactionResult
 * 
 * This class is transaction which contains output values for DUT.
 */
 
 class AluTransactionResult #(int pDataWidth = 8) extends BasicTransaction;

   //registration of component tools
   `ovm_object_utils(BasicTransactionResult)
   
   //included data
   bit EX_ALU_VLD;
   bit EX_ALU_RDY;
   logic [pDataWidth-1:0] EX_ALU;

  /*! 
   * Constructor - creates AluTransactionResult object  
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
      $write("EX_ALU_VLD: %d\n", EX_ALU_VLD);      
      $write("EX_ALU_RDY: %d\n", EX_ALU_RDY);  
      $write("EX_ALU: %d\n", EX_ALU);
      $write("\n");
   endfunction: display

  /*!
   * Copies the current value of the object instance to the specified object
   * instance. Returns a reference to the target instance.
   * 
   * \param to - original transaction        
   */
   virtual function AluTransactionResult copy(AluTransactionResult to = null);
   
     AluTransactionResult #(pDataWidth) tr;
     if (to == null)
       tr = new();
     else 
       $cast(tr, to);

     tr.EX_ALU_VLD  = EX_ALU_VLD;
     tr.EX_ALU_RDY  = EX_ALU_RDY;
     tr.EX_ALU   = EX_ALU;
             
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
   virtual function bit compare(input AluTransactionResult to, 
                                output string diff, input int kind = -1);
     bit same = 1; // Suppose that are same
     AluTransactionResult tr;
     $cast(tr, to);
       
     if (EX_ALU_VLD != tr.EX_ALU_VLD) 
     begin
       same = 0;
       $write(diff, "EX_ALU_VLD does not match!\n");
     end
       
     if (EX_ALU_RDY != tr.EX_ALU_RDY) 
     begin
       same = 0;
       $write(diff, "EX_ALU_RDY does not match!\n");
     end
     
     if (EX_ALU != tr.EX_ALU) 
     begin
       same = 0;
       $write(diff, "EX_ALU does not match!\n");
     end
     
     compare = same; 
   endfunction : compare 
   
 endclass: AluTransactionResult