/*
 * txbuff_transaction.sv: FrameLink Transaction
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
 * $Id: txbuff_transaction.sv 8606 2009-06-01 21:19:19Z xsimko03 $
 *
 * TODO:
 *
 */ 

  import sv_common_pkg::*; 
  
  // --------------------------------------------------------------------------
  // -- Tx Buffer Transaction Class
  // --------------------------------------------------------------------------
  /* This class describe transaction and simplyfy transaction random
   * generation.
   */
  
  class txBuffTransaction extends Transaction;
      
     // -- Public Class Atributes --
     // Randomization parameters
     int packetCount     = 1;  
     int flowCount       = 2;
     int packetSizeMax[] = '{32}; 
     int packetSizeMin[] = '{16};
     int num_block_addr;
     
     // Randomized transaction data [packet][byte]
     rand byte unsigned data[][];
         
     // -- Constrains --
     constraint c1 {
       data.size       == packetCount;
       num_block_addr inside {[0:(flowCount-1)]};
       foreach (data[i]) data[i].size inside
         {[packetSizeMin[i]:packetSizeMax[i]]};
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
       
       for (integer i=0; i < packetCount; i++) begin
         $write("Packet no: %d, Packet size: %d, Data:", i, data[i].size);
        
         for (integer j=0; j < data[i].size; j++)
         begin
           if (j%16==0) $write("\n\t%4x:",j);
           if (j%8==0) $write("\t");
           $write("%x ",data[i][j]);
         end  
         $write("\n");
       end    
     endfunction : display
 

  
     //-- Copy ----------------------------------------------------------------- 
     // Copy constructor
     virtual function Transaction copy(Transaction to = null);
       txBuffTransaction tr;
       if (tr == null)
         tr = new();
       else 
         $cast(tr, to);

       tr.packetCount   = packetCount;
       tr.num_block_addr= num_block_addr;
       tr.packetSizeMax = new[packetCount];
       tr.packetSizeMin = new[packetCount];
       tr.data          = new [packetCount];
       for (integer i=0; i < packetCount; i++)
         tr.data[i]     = new[data[i].size];

       tr.packetSizeMax = packetSizeMax;
       tr.packetSizeMin = packetSizeMin;
       tr.data=data;
       
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
       txBuffTransaction tr;
       $cast(tr, to);
       
       if (packetCount != tr.packetCount) 
       begin
         same = 0;
         diff = "packetCount does not match";
       end
       
       for (integer i=0; i<packetCount; i++)
       begin
         if (data[i].size != tr.data[i].size)
         begin 
           same = 0;
           diff = "packetSize[] does not match";
         end
       end
       
       for (integer i=0; i < packetCount; i++)   
         for (integer j=0; j < data[i].size; j++)
           if (data[i][j] != tr.data[i][j]) 
           begin
             same = 0;
             diff = "data[][] does not match";
           end
           
       compare = same;
     endfunction: compare 

   endclass: txBuffTransaction

