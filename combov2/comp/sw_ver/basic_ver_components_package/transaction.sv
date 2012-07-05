/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    Transaction Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */

 class Transaction;
  
   /*
    * Public Class Atributes
    */
    int data_id;   // data identifier
   
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
    endfunction : display
  
   /*!
    * Copies the current value of the object instance to the specified object
    * instance. Returns a reference to the target instance.
    * 
    * \param to - original transaction        
    */
    virtual function Transaction copy(Transaction to = null);
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
    * Configure HW registers according to constraints in SW in order to generate
    * transactions drectly in HW.    
    */
    virtual function void configureRegisters(int transCount);
    endfunction : configureRegisters  

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
    virtual function bit compare(input Transaction to, 
                                 output string diff, input int kind = -1);
      return 1'b0;
    endfunction : compare   
 endclass : Transaction  
 
   /*
    * Transaction mailbox
    */
    typedef mailbox #(Transaction) tTransMbx;

  
  
