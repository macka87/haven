/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    mi32_transaction
 * Description:  MI32 Transaction Class
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         24.4.2011 
 * ************************************************************************** */

 class Mi32Transaction extends Transaction;
      
   /*
    * Public Class Atributes
    */
    
   //! --- RANDOMIZATION OF TRANSACTION PARAMETERS ---
   
     logic [31:0] maxAddress = '1;
   
     rand logic [31:0]  address;
     rand logic [31:0]  data;
     rand logic [3:0]   be;
     rand logic         rw; // rw==0 => read request, rw==1 => write request

     // -- Constrains --
     constraint c1 {
       address       <= maxAddress;
       };

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
       
       if (rw == 0) // read request
         $write("Read from address: %0x data: %0x\n", address, data);
       else // write request
         $write("Write to address: %0x data: %0x BE: %0x\n", address, data, be);

    endfunction : display
 
   /*!
    * Copies the current value of the object instance to the specified object
    * instance. Returns a reference to the target instance.
    * 
    * \param to - original transaction        
    */
     virtual function Transaction copy(Transaction to = null);
       Mi32Transaction tr;
       if (to == null)
         tr = new();
       else 
         $cast(tr, to);

       tr.maxAddress    = maxAddress;
       tr.address       = address;
       tr.data          = data;
       tr.be            = be;
       tr.rw            = rw;

       copy = tr;
       endfunction: copy
       
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
       Mi32Transaction tr;
       if (! $cast(tr, to))
          $display("Cast error\n");
       
       if (address != tr.address) 
       begin
         same = 0;
         diff = "addresses does not match";
       end

       if (data != tr.data) 
       begin
         same = 0;
         diff = "data does not match";
       end

       if (rw != tr.rw) 
       begin
         same = 0;
         diff = "type/direction does not match";
       end

       if (be != tr.be) 
       begin
         same = 0;
         diff = "byte enable does not match";
       end

       compare = same;
    endfunction: compare 
 endclass: Mi32Transaction

