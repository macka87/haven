/*
 * au_transaction.sv: Align Unit Transaction
 * Copyright (C) 2008 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
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
 * $Id: au_transaction.sv 3590 2008-07-16 09:05:59Z xsanta06 $
 *
 * TODO:
 *
 */ 
  
  // --------------------------------------------------------------------------
  // -- Align Unit Transaction Class
  // --------------------------------------------------------------------------
  /* This class describe transaction and simplyfy transaction random
   * generation.
   */
  class AlignUnitTransaction extends Transaction;
      
     // -- Public Class Atributes --
     // Transaction length     
     int dataSizeMin = 8;
     int dataSizeMax = 512;
   
     // Randomized transaction data
     rand byte unsigned data[];

     // -- Constrains --
     constraint c1 {
       data.size inside {
                         [dataSizeMin:dataSizeMax]
                        };
       };


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
        
       $write("\nData length:%d\nData:\t\t",data.size);
       for (integer i=0; i < data.size; i++)
         $write("%x",data[i]);
       $write("\n");
   
    endfunction : display
 

  
     //-- Copy ----------------------------------------------------------------- 
     // Copy constructor
     virtual function Transaction copy(Transaction to = null);
       AlignUnitTransaction tr;
       if (tr == null)
         tr = new();
       else 
         $cast(tr, to);

       tr.dataSizeMin   = dataSizeMin;       
       tr.dataSizeMax   = dataSizeMax;
       tr.data          = new [data.size];
       tr.data          = data;
       
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
       AlignUnitTransaction tr;
       $cast(tr, to);
       
       if (data.size != tr.data.size) 
       begin
         same = 0;
         diff = "data length does not match";
       end
       
       
       for (integer i=0; i < data.size; i++)   
         if (data[i] != tr.data[i]) 
         begin
           same = 0;
           diff = "data[] does not match";
         end
           
       compare = same;
     endfunction: compare 
     
   endclass: AlignUnitTransaction

