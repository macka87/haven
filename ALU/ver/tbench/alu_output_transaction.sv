/* *****************************************************************************
 * Project Name: ALU Functional Verification
 * File Name:    alu_output_transaction.sv
 * Description:  Definition of output vectors (transactions)
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         22.3.2012 
 * ************************************************************************** */ 

class ALUOutTransaction #(int pDataWidth = 8) extends Transaction;
      
   /*
    * Public Class Atributes
    */
   
   logic [pDataWidth-1:0] alu_output;    // output of ALU unit
      
   /*
    * Public Class Methods
    */
    
   /*!
    * Function displays the current value of the transaction or data described
    * by this instance in a human-readable format on the standard output.
    *
    * \param prefix - transaction type
    */
    virtual function void display(string prefix = "");
      if (prefix != "")
       begin
         $write("---------------------------------------------------------\n");
         $write("-- %s\n",prefix);
         $write("---------------------------------------------------------\n");
       end
       
       $write("alu_output: %d\n", alu_output);  
       $write("\n");  
    endfunction : display
 
   /*!
    * Compares the current value of the object instance with the current value
    * of the specified object instance, according to the specified kind. Returns
    * TRUE (i.e., non-zero) if the value is identical. If the value is 
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
    virtual function bit compare(input Transaction to, 
                                 output string diff, input int kind = -1);
      bit same = 1; // Suppose that are same
      ALUOutTransaction #(pDataWidth) tr;
      $cast(tr, to);
       
      if (alu_output != tr.alu_output) 
      begin
        same = 0;
        $write(diff, "ALU_OUTPUT does not match!\n");
        $write("EXPECTED TRANSACTION: %d\n", alu_output);
        $write("\n");
      end
       
      compare = same;  
    endfunction: compare 
 endclass: ALUOutTransaction
