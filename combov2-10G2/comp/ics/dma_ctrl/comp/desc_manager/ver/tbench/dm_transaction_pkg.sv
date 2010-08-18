/*
 * dm_transaction_pkg.sv: Transaction for Descriptor Manager
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
 * $Id: dm_transaction_pkg.sv 4095 2008-07-29 07:39:27Z xsimko03 $
 *
 * TODO:
 *
 */ 

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package dm_transaction_pkg; 
  
  import sv_common_pkg::*; 
  // --------------------------------------------------------------------------
  // -- Descriptor Manager Transaction Class
  // --------------------------------------------------------------------------
  /* This class describe transaction and simplyfy transaction random
   * generation.
   */
  
  class descManagerTransaction extends Transaction;
      
     // -- Public Class Atributes --
     // Randomization parameters
     int dataSize     = 64;
     
     
     rand bit unsigned [63:0] data;
     
     
     
     // Randomized transaction data [packet][byte]
     //for (int i=0; i<12; i++)
     //  data[i]=0;
     //for (int i=12; i<64; i++)  
     //  rand bit unsigned data[i];
    // rand int unsigned num_block_addr;

     // -- Constrains --
     constraint c1 {
       data[11:0]==0;
       //num_block_addr inside {[0:(flowCount-1)]};
       };


    // -- Public Class Methods --
  
    /*
     * Displays the current value of the transaction or data described by this
     * instance in a human-readable format on the standard output. Each line of
     * the output will be prefixed with the specified prefix. This method prints
     * the value returned by the psdisplay() method.
     */
    virtual function void display(string prefix = "");
       byte unsigned dataToWrite[] = new [dataSize/8];
       int m=0;
       
       if (prefix != "")
       begin
         $write("---------------------------------------------------------\n");
         $write("-- %s\n",prefix);
         $write("---------------------------------------------------------\n");
       end
//       $write("dataToWrite.size:%d\n",dataToWrite.size);
    //   $write("Block_addr: %d Data: ", num_block_addr);      
       
       for (int i=0; i<dataToWrite.size; i++)
         for (int j=0; j<8; j++)
           dataToWrite[i][j]=data[m++];
       
       for (integer j=0; j < dataToWrite.size; j++)
         $write("%x",dataToWrite[j]);
       $write("\n");
    
    endfunction : display
 

  
     //-- Copy ----------------------------------------------------------------- 
     // Copy constructor
     virtual function Transaction copy(Transaction to = null);
       descManagerTransaction tr;
       if (tr == null)
         tr = new();
       else 
         $cast(tr, to);

       tr.dataSize       = dataSize; 
   //    tr.flowCount      = flowCount;
   //    tr.num_block_addr = num_block_addr;
       
       
       tr.data = data;
       
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
       descManagerTransaction tr;
       $cast(tr, to);
       
       
       
   //    if (num_block_addr != tr.num_block_addr)
   //      begin
   //        same = 0;
   //        diff = "BlockAddr does not match";
   ///      end 
       
       for (integer i=0; i < 64; i++)
         if (data[i] != tr.data[i]) 
           begin
             same = 0;
             diff = "data[] does not match";
           end
           
       compare = same;
     endfunction: compare 

   endclass: descManagerTransaction

endpackage : dm_transaction_pkg