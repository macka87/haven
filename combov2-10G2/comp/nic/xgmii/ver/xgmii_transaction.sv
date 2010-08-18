/*
 * \file xgmii_transaction.sv
 * \brief XGMII Transaction
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
 * $Id: xgmii_transaction.sv 14064 2010-06-16 12:38:59Z xsanta06 $
 *
 * TODO:
 *
 */

  import crc32_pkg::*;     // Import CRC functions

  // --------------------------------------------------------------------------
  // -- XGMII Transaction Class
  // --------------------------------------------------------------------------
  /*!
   * \brief XGMII Transaction Class
   * 
   * This class describe XGMII transaction and simplyfy transaction random
   * generation.
   */
  class XgmiiTransaction extends Transaction;

    // -- Public Class Atributes --
    //! Randomization parameters
     //! Maximal data size
    int dataSizeMax = 1518; 
     //! Minimal data size
    int dataSizeMin = 60;
     //! Enable XGMII error weight
    int xgmiiErrorEn_wt  = 1;
     //! Disable XGMII error weight
    int xgmiiErrorDis_wt = 10;
     //! Enable CRC error weight
    int crcErrorEn_wt    = 0;
     //! Disable CRC error weight
    int crcErrorDis_wt   = 1;

   
    //! Randomized transaction data
    rand byte unsigned data[];

    //! Randomized XGMII error flag
    rand bit xgmiiError;
    //! Randomized XGMII error position
    rand int unsigned xgmiiErrorPos;
    //! Randomized CRC error flag
    rand bit crcError;
    //! Transaction CRC
    byte unsigned crc[] = new[4];

    // -- Constrains --
    constraint c1 {
      (data.size + crc.size) inside {
                               [dataSizeMin:dataSizeMax]
                                    };

      crcError dist { 1'b1 := crcErrorEn_wt,
                      1'b0 := crcErrorDis_wt
                    };

      xgmiiError dist { 1'b1 := xgmiiErrorEn_wt,
                        1'b0 := xgmiiErrorDis_wt
                      };

      xgmiiErrorPos inside {
                            [0:(data.size + crc.size)]
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
    function void display(string prefix="");
      if (prefix != "")
      begin
        $write("---------------------------------------------------------\n");
        $write("-- %s\n",prefix);
        $write("---------------------------------------------------------\n");
      end
       
      $write("Data size: %1d, Data:", data.size);
       
      for (int i=0; i < data.size; i++) 
      begin
        if (i%16==0) $write("\n%4x:",i);
        if (i%8==0) $write(" ");
        $write("%x ",data[i]);
      end  
      $write("\n\n");

      if(crcError) $write("Error was injected into CRC\n");

      $write("CRC: ");
      for (int i=0; i < crc.size; i++)
        $write("%x ",crc[i]);
      $write("\n");

      if(xgmiiError) $write("Error was injected into XGMII packet\n");

    endfunction: display
  
    //------------------------------------------------------------------------- 
    //! Copy
    /*!
     * Copy constructor
     *
     * \param to - 
     */
    virtual function Transaction copy(Transaction to = null);
      XgmiiTransaction tr;
      if (to == null)
        tr = new();
      else 
        $cast(tr, to);

      tr.dataSizeMax      = dataSizeMax;
      tr.dataSizeMin      = dataSizeMin;
      tr.xgmiiErrorEn_wt  = xgmiiErrorEn_wt;
      tr.xgmiiErrorDis_wt = xgmiiErrorDis_wt;
      tr.crcErrorEn_wt    = crcErrorEn_wt;
      tr.crcErrorDis_wt   = crcErrorDis_wt;
      tr.data             = new [data.size];
      tr.crc              = new [crc.size];

      tr.data             = data;
      tr.xgmiiError       = xgmiiError;
      tr.xgmiiErrorPos    = xgmiiErrorPos;
      tr.crcError         = crcError;
      tr.crc              = crc; 

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
      XgmiiTransaction tr;
      $cast(tr, to);
      
      if (data.size != tr.data.size)
      begin 
        same = 0;
        $swrite(diff, "dataSize does not match");
      end
      
      for (int i=0; i < data.size; i++)
        if (data[i] != tr.data[i]) 
        begin
          same = 0;
          $swrite(diff, "data[%0d] does not match", i);
        end

      if (kind == -1) 
        for (int i=0; i<crc.size; i++)
          if (crc[i] != tr.crc[i]) 
          begin
            same = 0;
            $swrite(diff, "crc[%0d] does not match", i);
          end
          
      compare = same;
    endfunction: compare 


    // -- Private Class Methods --

    //------------------------------------------------------------------------- 
    //! Post Randomize
    /*!
     * Function is called after randomization. It computes correct CRC or
     * inject error into it.
     */
    function void post_randomize();
      int badBytePos;
      byte badByte;
      bit [31:0] crcValue;

      // Compute correct CRC
      crcValue = crcCompute(data);
      for(int i=0; i<4; i++)
        for (int j=0; j<8; j++)
          crc[i][j] = crcValue[i*8+j];

      // Inject CRC Error
      if(crcError) begin
        badBytePos = $urandom_range(crc.size - 1);
        do begin
          badByte = $urandom();
        end while (badByte == crc[badBytePos]);
        
        crc[badBytePos] = badByte;
      end
    endfunction : post_randomize

  endclass : XgmiiTransaction
