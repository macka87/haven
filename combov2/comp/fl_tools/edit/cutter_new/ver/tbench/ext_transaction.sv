/*
 * ext_transaction.sv: Extraction data Transaction
 * Copyright (C) 2009 CESNET
 * Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 * 3. Neither the name of the Company nor the names of its contributors
 *    may be used to endorse or promote products derived from this
 *    software without specific prior written permission.
 *
 * This software is provided ``as is'', and any express or implied
 * warranties, including, but not limited to, the implied warranties of
 * merchantability and fitness for a particular purpose are disclaimed.
 * In no event shall the company or contributors be liable for any
 * direct, indirect, incidental, special, exemplary, or consequential
 * damages (including, but not limited to, procurement of substitute
 * goods or services; loss of use, data, or profits; or business
 * interruption) however caused and on any theory of liability, whether
 * in contract, strict liability, or tort (including negligence or
 * otherwise) arising in any way out of the use of this software, even
 * if advised of the possibility of such damage.
 *
 * $Id: ext_transaction.sv 10700 2009-08-25 14:44:13Z xstour03 $
 *
 * TODO:
 *
 */ 

  // --------------------------------------------------------------------------
  // -- Extraction data Transaction Class
  // --------------------------------------------------------------------------
  /* This class describe transaction and simplyfy transaction random
   * generation.
   */
  class ExtDataTransaction extends Transaction;
      
     // -- Public Class Atributes --
     // Randomization parameters
   
     // Randomized transaction data [byte]
     rand byte unsigned ext_data[];
     int ext_done;
     int ext_err;
     int op_size; //original size of part or size of extracted data from extraction which ended with error
     

    // -- Public Class Methods --
  
    /*
     * Displays the current value of the transaction or data described by this
     * instance in a human-readable format on the standard output. Each line of
     * the output will be prefixed with the specified prefix. This method prints
     * the value returned by the psdisplay() method.
     */
    virtual function void display(string prefix = "");
       if (prefix != "")
       begin
         $write("---------------------------------------------------------\n");
         $write("-- %s\n",prefix);
         $write("---------------------------------------------------------\n");
       end
       
       $write("Extracted data:");
        
       for (integer j=0; j < ext_data.size; j++) 
       begin
         if (j%16==0) $write("\n%4x:",j);
         if (j%8==0) $write(" ");
         $write("%x ",ext_data[j]);
       end  
       $write("\nExtracted DONE value: %d", ext_done);
       $write("\nExtracted ERR value:  %d", ext_err);
      // $write("\nOriginal part size:   %d", op_size);
       $write("\n");  
    endfunction : display
 

  
     //-- Copy ----------------------------------------------------------------- 
     // Copy constructor
     virtual function Transaction copy(Transaction to = null);
       ExtDataTransaction tr;
       if (to == null)
         tr = new();
       else 
         $cast(tr, to);

       tr.ext_data      = new[ext_data.size](ext_data);
       tr.ext_done      = ext_done;
       tr.ext_err       = ext_err;
       tr.op_size       = op_size;
       
       copy = tr;
       endfunction: copy
       
 	   
     // -- Compare --------------------------------------------------------------
     /* Compares the current value of the object instance with the current value
      * of the specified object instance, according to the specified kind.
      * Returns TRUE (i.e., non-zero) if the value is identical. If the value is
      * different, FALSE is returned and a descriptive text of the first 
      * difference found is returned in the specified stringvariable. The kind 
      * argument may be used to implement different comparison functions (e.g., 
      * full compare, comparison of rand properties only, comparison of all 
      * properties physically implemented in a protocol and so on.)
      */    
     virtual function bit compare(input Transaction to, 
                                  output string diff, input int kind = -1);
       bit same = 1; // Suppose that are same
       ExtDataTransaction tr;
       $cast(tr, to);
       
       if (ext_done != tr.ext_done)
       begin
          same = 0;
          $swrite(diff, "Unknown transaction received");
       end

       if (ext_err != tr.ext_err)
       begin
          same = 0;
          $swrite(diff, "Unknown transaction received");
       end

       if ((ext_done == 1) && (ext_err == 0))
       begin
          //extraction is ok, then extracted data should match
          if (ext_data.size != tr.ext_data.size)
          begin 
            same = 0;
            $swrite(diff, "Extraction data are different lengths");
          end
          
          for (integer j=0; j < ext_data.size; j++)
            if (ext_data[j] != tr.ext_data[j]) 
            begin
              same = 0;
              $swrite(diff, "Extraction data[%0d] does not match", j);
            end
       end

       if ((ext_done == 1) && (ext_err == 1))
       begin
          //extraction was interrupted due to lack of data
          if (tr.op_size > 0)
             for (integer j=0; j < tr.op_size; j++)
                if (ext_data[j] != tr.ext_data[j])
                begin
                   same = 0;
                   $swrite(diff, "Extraction data[%0d] does not match", j);
                end
       end
           
       compare = same;
     endfunction: compare 

   endclass: ExtDataTransaction

