/*
 * su_transaction.sv: Status Update Transaction
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
 * $Id: su_transaction.sv 10685 2009-08-25 12:16:22Z xsanta06 $
 *
 * TODO:
 *
 */ 

  // --------------------------------------------------------------------------
  // -- Status Update Transaction Class
  // --------------------------------------------------------------------------
  /* This class describe transaction and simplyfy transaction random
   * generation.
   */
  class StatusUpdateTransaction extends Transaction;
      
    // -- Public Class Atributes --
    // Randomization parameters
    int maxAddress    = 4;     
    int dataSize      = 24;
    bit rxType        = 0; // True == rx type, False == tx type
    // Set/Reset interrupt flag (weights)
    int intFlag1_wt   = 1; 
    int intFlag0_wt   = 10;
    // Set/Reset last fragment flag (weights)
    int lfFlag1_wt    = 15; 
    int lfFlag0_wt    = 1;
   
    // Randomized transaction data 
    rand bit intFlag;   // Status Update interrupt flag
    rand bit lfFlag;    // Status Update last fragment flag
    rand int unsigned address;   // Status Update address
    rand logic [15:0] length;    // Data length (RX only)

    bit data[];

    // -- Constrains --
    constraint c1 {
      intFlag dist { 1'b1 := intFlag1_wt,
                     1'b0 := intFlag0_wt
                   };

      lfFlag dist { 1'b1 := lfFlag1_wt,
                    1'b0 := lfFlag0_wt
                  };

      if (lfFlag==0) intFlag!=1;

      address < maxAddress;

      length < 'h10000;
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
       
      if (rxType) $write("Type: RX\n");
      else $write("Type: TX\n");

      $write("Address: %0x, Length: %0x, INTF: %0b, LFF: %0b\n", 
             address, length, intFlag, lfFlag);

      $write("Data: ");
      for (int i=0; i<data.size; i++)
        $write("%0b",data[i]); 
      $write("\n");  

    endfunction : display
 

  
     //-- Copy ----------------------------------------------------------------- 
     // Copy constructor
     virtual function Transaction copy(Transaction to = null);
       StatusUpdateTransaction tr;
       if (to == null)
         tr = new();
       else 
         $cast(tr, to);

       tr.maxAddress  = maxAddress;
       tr.intFlag1_wt = intFlag1_wt;
       tr.intFlag0_wt = intFlag0_wt;
       tr.lfFlag1_wt  = lfFlag1_wt;
       tr.lfFlag0_wt  = lfFlag0_wt;
       tr.dataSize = dataSize;
       tr.rxType   = rxType; 
       tr.intFlag  = intFlag;
       tr.lfFlag   = lfFlag; 
       tr.address  = address;
       tr.length   = length; 
       tr.data     = data;   
       
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
       StatusUpdateTransaction tr;
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
       
       if (address != tr.address) 
       begin
         same = 0;
         $swrite(diff, "Address does not match");
       end
       
       if (length != tr.length) 
       begin
         same = 0;
         $swrite(diff, "Length does not match");
       end
       
       if (data != tr.data) 
       begin
         same = 0;
         $swrite(diff, "Data does not match");
       end
       
       compare = same;
     endfunction: compare 

     // -- Post Randomize ----------------------------------------------------
     // Allocate and fill up data variable with flags and length
     function void post_randomize();
       data = new[dataSize];

       // RX status update
       if (rxType) begin
         for (int i=0; i<16; i++)
           data[i] = length[i];
         data[16] = intFlag;
         data[17] = lfFlag;
       end
       // TX status update
       else data = {intFlag, lfFlag, '0};
     endfunction: post_randomize

   endclass: StatusUpdateTransaction

