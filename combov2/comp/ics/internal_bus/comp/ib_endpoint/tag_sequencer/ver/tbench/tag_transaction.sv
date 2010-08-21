/*
 * \file tag_transaction.sv
 * \brief TAG SEQUENCER Transaction
 * \author Marek Santa <santa@liberouter.org>
 * \date 2010 
 */
 /*
 * Copyright (C) 2010 CESNET
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
 * $Id: tag_transaction.sv 14346 2010-07-13 13:38:11Z xsanta06 $
 *
 * TODO:
 *
 */

  // --------------------------------------------------------------------------
  // -- TAG Transaction Class
  // --------------------------------------------------------------------------
  /*!
   * \brief TAG Transaction Class
   * 
   * This class describe TAG transaction and simplyfy transaction random
   * generation.
   */
  class TagTransaction #(int pTagWidth = 8) extends Transaction;

    // -- Public Class Atributes --
    //! Randomized transaction data
    rand bit[pTagWidth-1:0] tag;
    rand bit[1:0]           transType;

    constraint c {
      transType[0] == tag[0];
    }


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
    function void display(string prefix="");
      if (prefix != "")
      begin
        $write("---------------------------------------------------------\n");
        $write("-- %s\n",prefix);
        $write("---------------------------------------------------------\n");
      end
       
      $write("\nTag: %0d Trans Type[0]: %0d\n", tag, transType[0]);

    endfunction: display
  
    //------------------------------------------------------------------------- 
    //! Copy
    /*!
     * Copy constructor
     *
     * \param to - 
     */
    virtual function Transaction copy(Transaction to = null);
      TagTransaction #(pTagWidth) tr;
      if (to == null)
        tr = new();
      else 
        $cast(tr, to);

      tr.tag         = tag;
      tr.transType   = transType;

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
      TagTransaction #(pTagWidth) tr;
      $cast(tr, to);
      
      if (tag != tr.tag)
      begin 
        same = 0;
        $swrite(diff, "tag does not match");
      end
      
      if (transType[0] != tr.transType[0])
      begin 
        same = 0;
        $swrite(diff, "transaction type does not match");
      end
      
      compare = same;
    endfunction: compare 

    // -- Private Class Methods --

  endclass : TagTransaction
