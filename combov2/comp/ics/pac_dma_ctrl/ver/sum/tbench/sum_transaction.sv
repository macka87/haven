/*
 * sum_transaction.sv: Status Update Manager Transaction
 * Copyright (C) 2009 CESNET
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
 * $Id: sum_transaction.sv 10496 2009-08-19 05:27:17Z xsanta06 $
 *
 * TODO:
 *
 */ 

  // --------------------------------------------------------------------------
  // -- Status Update Manager Transaction Class
  // --------------------------------------------------------------------------
  /* This class describe transaction and simplyfy transaction random
   * generation.
   */
  class SumTransaction extends Transaction;
      
    // -- Public Class Atributes --
   
    // -- Public Class Atributes
    longint descAddr      = 0;
    bit     intFlag       = 0;
    bit     lfFlag        = 0;
    int     length        = 0;


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
       
      $write("Descriptor Address: %0x, INTF: %0b, LFF: %0b, length: %0x\n",
             descAddr, intFlag, lfFlag, length);

    endfunction : display
 

  
     //-- Copy ----------------------------------------------------------------
     // Copy constructor
     virtual function Transaction copy(Transaction to = null);
       SumTransaction tr;
       if (to == null)
         tr = new();
       else 
         $cast(tr, to);

       tr.descAddr   = descAddr; 
       tr.length     = length;
       tr.intFlag    = intFlag; 
       tr.lfFlag     = lfFlag; 
       
       copy = tr;
     endfunction: copy

     // -- Compare ------------------------------------------------------------
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
       SumTransaction tr;
       $cast(tr, to);
       
       if (intFlag != tr.intFlag) 
       begin
         same = 0;
         $swrite(diff, "Interrupt flag does not match");
       end
       
       if (lfFlag != tr.lfFlag) 
       begin
         same = 0;
         $swrite(diff, "Last fragment  flag does not match");
       end
       
       if (descAddr != tr.descAddr) 
       begin
         same = 0;
         $swrite(diff, "Address does not match");
       end
       
       if (length != tr.length) 
       begin
         same = 0;
         $swrite(diff, "Length does not match");
       end
       
       compare = same;
     endfunction: compare 

   endclass: SumTransaction

