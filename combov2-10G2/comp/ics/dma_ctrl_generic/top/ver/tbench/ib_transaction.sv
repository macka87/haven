/*
 * \file ib_transaction.sv
 * \brief Internal Bus Transaction
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
 * $Id: ib_transaction.sv 14904 2010-08-06 10:47:46Z xspinl00 $
 *
 * TODO:
 *
 */
  
  // -- Internal Bus Transaction Types Constants ------------------------------
  //! Local to Local Write
  const logic [3:0] L2LW_TYPE = 4'b0001; 
  //! Local to Local Read
  const logic [3:0] L2LR_TYPE = 4'b0000; 
  //! Local to Global Write
  const logic [3:0] L2GW_TYPE = 4'b0011; 
  //! Global to Local Read
  const logic [3:0] G2LR_TYPE = 4'b0010; 
  //! Read completition
  const logic [3:0] RDC_TYPE  = 4'b1101; 

  //! Internal Bus Transaction Types 
  typedef enum {L2LW=0, L2LR=1, L2GW=2, G2LR=3, RDC=13} eTransactionType;

  // --------------------------------------------------------------------------
  // -- Internal Bus Transaction Class
  // --------------------------------------------------------------------------
 
  /*!
   * \brief Internal Bus Transaction Class
   * 
   * This class describe IB transaction
   */
  class InternalBusTransaction;

    // -- Public Class Atributes --
    
    //! Transaction Local Address
    logic [31:0]     localAddr;  
    //! Transaction Global Address
    logic [63:0]     globalAddr; 
    //! Transaction Tag
    logic [15:0]     tag;  
    //! Transaction Length      
    logic [11:0]     length; 
    //! Transaction Type    
    eTransactionType transType; 
    //! Transaction Data 
    logic [7:0] data[];          

    // -- Public Class Methods --

    //! Show transaction 
    /*
     * Function show transaction in text format
     * \param full - shows also data    
     */      
    function void display(integer full=0);
      $write("Transaction LOCAL_ADDR=%0x, GLOBAL_ADDR=%0x, TAG=%0x, \
              LENGTH=%0x, TYPE=", localAddr, globalAddr, tag, length);
      case (transType)
        L2LW:
          $write("L2LW\n");
        L2LR:
          $write("L2LR\n");
        L2GW:
          $write("L2GW\n");
        G2LR:
          $write("G2LR\n");
        RDC:
          $write("RDC\n");
      endcase;

      // Write also data for specified transaction types
      if (full && (transType == L2LW || transType == L2GW || transType == RDC))
      for (integer i=0; i < data.size; i=i+8)
        for (integer j = i+7; j >= i; j--) begin
          if (j==i+7)
            $write("DATA: 0x");
          if (j < data.size)
            $write("%x", data[j]);
          else
            $write("00");
          if (j == i)
            $write("\n");
      end
    endfunction: display

  endclass : InternalBusTransaction
