/*
 * mi32_transaction.sv: Mi32 Transaction
 * Copyright (C) 2008 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
 *            Petr Kastovsky <kastovsky@liberouter.org>
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
 * $Id: mi32_transaction.sv 10386 2009-08-14 05:37:32Z xsanta06 $
 *
 * TODO:
 *
 */ 

  // --------------------------------------------------------------------------
  // -- Mi32 Transaction Class
  // --------------------------------------------------------------------------
  /* This class describe transaction and simplyfy transaction random
   * generation.
   */
  class Mi32Transaction extends Transaction;
      
     // -- Public Class Atributes --
     // Randomization parameters
     logic [31:0] maxAddress = '1;
   
     // Randomized transaction parameters
     rand logic [31:0]  address;
     rand logic [31:0]  data;
     rand logic [3:0]   be;
     rand logic         rw; // rw==0 => read request, rw==1 => write request

     // -- Constrains --
     constraint c1 {
       address       <= maxAddress;
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
       
       if (rw == 0) // read request
         $write("Read from address: %0x data: %0x\n", address, data);
       else // write request
         $write("Write to address: %0x data: %0x BE: %0x\n", address, data, be);

    endfunction : display
 

  
     //-- Copy ----------------------------------------------------------------- 
     // Copy constructor
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

