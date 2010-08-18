/*
 * sum_rf_transaction.sv: Request Fifo Transaction
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
 * $Id: sum_rf_transaction.sv 10722 2009-08-26 08:10:54Z xsanta06 $
 *
 * TODO:
 *
 */ 

  // --------------------------------------------------------------------------
  // -- SUM Request Fifo Transaction Class
  // --------------------------------------------------------------------------
  /* This class describe transaction and simplyfy transaction random
   * generation.
   */
  class SumRfTransaction extends Transaction;
      
    // -- Public Class Atributes --
    // Randomization parameters
    int blockSize    = 4;     
   
    // Randomized transaction data 
    rand int unsigned blockLength;   // RF block length
    rand int unsigned descStartAddr; // Address of first descriptor

    int rfRAddr      = 0;

    // -- Constrains --
    constraint c1 {
      blockLength inside {
                          [1:blockSize]
                         };

      descStartAddr%16 == 0;
      descStartAddr/16'h1000 == (descStartAddr+(16*blockLength))/16'h1000;
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
       
      $write("Descriptor Start Address:%0x, Block length:%0x, RF Address:%0x\n",
             descStartAddr, blockLength, rfRAddr);

    endfunction : display
 

  
     //-- Copy ----------------------------------------------------------------
     // Copy constructor
     virtual function Transaction copy(Transaction to = null);
       SumRfTransaction tr;
       if (to == null)
         tr = new();
       else 
         $cast(tr, to);

       tr.blockSize       = blockSize;
       tr.descStartAddr   = descStartAddr; 
       tr.blockLength     = blockLength;
       tr.rfRAddr         = rfRAddr; 
       
       copy = tr;
     endfunction: copy

   endclass: SumRfTransaction

