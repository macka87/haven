/*
 * \file pcd_transaction.sv
 * \brief PACODAG Transaction
 * \author Marek Santa <xsanta06@stud.fit.vutbr.cz>
 * \date 2009 
 */
 /*
 * Copyright (C) 2009 CESNET
 * 
 * LICENSE TERMS 
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
 * $Id: pcd_transaction.sv 12329 2009-12-24 01:04:25Z xsanta06 $
 *
 * TODO:
 *
 */

  // --------------------------------------------------------------------------
  // -- PACODAG Transaction Class
  // --------------------------------------------------------------------------
  /*!
   * \brief PACODAG Transaction Class
   * 
   * This class describe PACODAG transaction and simplyfy transaction random
   * generation.
   */
  class PacodagTransaction extends Transaction;

    // -- Public Class Atributes --
    //! Randomization parameters
     //! Number of packet parts
    int partCount     = 2; 
     //! Maximal part size
    int partSizeMax[] = '{32,32};
     //! Minimal part size
    int partSizeMin[] = '{ 8, 8};
   
    //! Randomized transaction data [part][byte]
    rand byte unsigned data[][];

    // -- Constrains --
    constraint c1 {
      data.size       == partCount;

      foreach (data[i]) 
        data[i].size inside {
                             [partSizeMin[i]:partSizeMax[i]]
                            };
      };
    

    // -- Public Class Methods --

    // ------------------------------------------------------------------------
    //! Display transaction 
    /*!
     * Displays the current value of the transaction or data described by this
     * instance in a human-readable format on the standard output. Each line of
     * the output will be prefixed with the specified prefix. This method prints
     * the value returned by the psdisplay() method.
     *
     * \param prefix - output prefix    
     */      
    virtual function void display(string prefix = "");
       if (prefix != "")
       begin
         $write("---------------------------------------------------------\n");
         $write("-- %s\n",prefix);
         $write("---------------------------------------------------------\n");
       end
       
       for (integer i=0; i < partCount; i++) begin
         $write("Part no: %1d, Part size: %1d, Data:", i, data[i].size);
        
         for (integer j=0; j < data[i].size; j++) 
         begin
           if (j%16==0) $write("\n%4x:",j);
           if (j%8==0) $write(" ");
           $write("%x ",data[i][j]);
         end  
         $write("\n");
       end  
       $write("\n");  
    endfunction : display
 
    //------------------------------------------------------------------------- 
    //! Copy
    /*!
     * Copy constructor
     *
     * \param to - 
     */
     virtual function Transaction copy(Transaction to = null);
       PacodagTransaction tr;
       if (to == null)
         tr = new();
       else 
         $cast(tr, to);

       tr.partCount   = partCount;
       tr.partSizeMax = new[partCount];
       tr.partSizeMin = new[partCount];
       tr.data        = new [partCount];
       for (integer i=0; i < partCount; i++)
         tr.data[i]   = new[data[i].size];

       tr.partSizeMax = partSizeMax;
       tr.partSizeMin = partSizeMin;
       tr.data        = data;
       
       copy = tr;
       endfunction: copy
       
    // -------------------------------------------------------------------------
    //! Compare
    /*!
     * Compares the current value of the object instance with the current value
     * of the specified object instance, according to the specified kind.
     * Returns TRUE (i.e., non-zero) if the value is identical. If the value is
     * different, FALSE is returned and a descriptive text of the first 
     * difference found is returned in the specified stringvariable. The kind 
     * argument may be used to implement different comparison functions (e.g., 
     * full compare, comparison of rand properties only, comparison of all 
     * properties physically implemented in a protocol and so on.)
     *
     * \param to - compared transaction
     * \param diff - difference between compared transaction
     * \param kind - type of comparison
     */    
     virtual function bit compare(input Transaction to, 
                                  output string diff, input int kind = -1);
       bit same = 1; // Suppose that are same
       PacodagTransaction tr;
       $cast(tr, to);
       
       if (partCount != tr.partCount) 
       begin
         same = 0;
         $swrite(diff, "partCount does not match");
       end
       
       for (integer i=0; i<partCount; i++)
       begin
         if (data[i].size != tr.data[i].size)
         begin 
           same = 0;
           $swrite(diff, "partSize[%0d] does not match", i);
         end
       end
       
       for (integer i=0; i < partCount; i++)   
         for (integer j=0; j < data[i].size; j++)
           if (data[i][j] != tr.data[i][j]) 
           begin
             same = 0;
             $swrite(diff, "data[%0d][%0d] does not match", i, j);
           end
           
       compare = same;
     endfunction: compare 

  endclass : PacodagTransaction
