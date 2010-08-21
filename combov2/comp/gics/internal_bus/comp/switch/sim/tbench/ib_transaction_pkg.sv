/*
 * ib_transaction_pkg.sv: Internal Bus Transaction
 * Copyright (C) 2008 CESNET
 * Author(s): Tomas Malek <tomalek@liberouter.org>
 *            Petr Kobiersky <kobiersky@liberouter.org>
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
 * $Id: ib_transaction_pkg.sv 1364 2008-02-18 15:23:10Z tomalek $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package ib_transaction_pkg; 
  
  // -- Internal Bus Transaction Types Constants ------------------------------

  // -- 3.bit: not last/last, 2.bit: norm/cpl, 1.bit: local/global, 0.bit: no data/with data 
  const logic [3:0] L2LR_TYPE = 4'b0000;
  const logic [3:0] L2LW_TYPE = 4'b0001;
  const logic [3:0] G2LR_TYPE = 4'b0010;
  const logic [3:0] L2GW_TYPE = 4'b0011;
  const logic [3:0] RDC_TYPE  = 4'b0101;
  const logic [3:0] RDCL_TYPE = 4'b1101;       

  // -- Internal Bus Transaction Types ----------------------------------------
  typedef enum {L2LW=1, L2LR=0, L2GW=3, G2LR=2, RDC=5, RDCL=13} eTransactionType;

  // --------------------------------------------------------------------------
  // -- Internal Bus Transaction Class
  // --------------------------------------------------------------------------
  /* This class describe transaction and simplyfy transaction random
   * generation.
   */
  class InternalBusTransaction;

    // -- Public Class Atributes --
    rand logic [31:0]     localAddr;  // Transaction Local Address
    rand logic [63:0]     globalAddr; // Transaction Global Address
    rand logic [ 7:0]     tag;        // Transaction Tag
    rand logic [11:0]     length;     // Transaction Length
    rand eTransactionType transType;  // Transaction Type
    logic [7:0] data[];               // Transaction Data

    // Delay attributes
    rand bit enTxDelay;           // Enable Tx Delay
    rand bit enInsideTxDelay;     // Enable Inside Tx Delay
    rand integer txDelay;         // Wait txDelay clock cycles before sending
    
    // Transaction types probability weights (set 0 to switch off)
    int L2LW_wt = 1; // Local to Local Write
    int L2LR_wt = 1; // Local to Local Read
    int L2GW_wt = 1; // Local to Global Write
    int G2LR_wt = 1; // Global to Local Read
    int RDC_wt  = 1; // Read completition (not last packet)
    int RDCL_wt = 1; // Read completition (last packet)

    // Delay weights
    int txDelayEn_wt             = 1; 
    int txDelayDisable_wt        = 5;
    int insideTxDelayEn_wt       = 1; 
    int insideTxDelayDisable_wt  = 5;

    // Transaction parameter limits
    logic [31:0] localAddrLow   = 32'h00000000;
    logic [31:0] localAddrHigh  = 32'h66666666;
    logic [63:0] globalAddrLow  = 64'h000000000000000;
    logic [63:0] globalAddrHigh = 64'h666666666666666;
    logic [15:0] tagLow         =  8'h00;
    logic [15:0] tagHigh        =  8'hFF;
    logic [11:0] lengthLow      = 12'h001;
    logic [11:0] lengthHigh     = 12'h050;

    // Delays limits
    int txDelayLow          = 0;
    int txDelayHigh         = 3;
    int insideTxDelay       = 3; // Maximal delay between transaction words


    // -- Private Class Atributes --
    
    // -- Constrains --

    // Constrain for Transactions Types
    constraint cTransactions {
      transType dist { L2LW := L2LW_wt, L2LR := L2LR_wt,
                       L2GW := L2GW_wt, G2LR := G2LR_wt,
                       RDC  := RDC_wt,  RDCL := RDCL_wt};
    }

    // Constrain for Data ranges
    constraint cRanges {
      localAddr  inside {[localAddrLow:localAddrHigh]};
      globalAddr inside {[globalAddrLow:globalAddrHigh]};
      tag        inside {[tagLow:tagHigh]};
      length     inside {[lengthLow:lengthHigh]};
    }

    // Delays constrains
    constraint cDelays {
      txDelay inside {[txDelayLow:txDelayHigh]};
      enTxDelay dist { 1'b1 := txDelayEn_wt,
                       1'b0 := txDelayDisable_wt};
      enInsideTxDelay dist { 1'b1 := insideTxDelayEn_wt,
                             1'b0 := insideTxDelayDisable_wt};
    }

    // -- Public Class Methods --
  
    //-- Random intertransaction wait -----------------------------------------
    function integer getRandomWait();
       if (enInsideTxDelay)
         return $urandom_range(insideTxDelay);
      else
         return 0;
    endfunction : getRandomWait

    //-- Copy ----------------------------------------------------------------- 
    // Copy constructor
    virtual function InternalBusTransaction copy();
       copy = new;
       copyData(copy);
    endfunction : copy

    //-- Compare -------------------------------------------------------------- 
    // Compare transaction with another. Return 1 for same transactions
    function int compare(InternalBusTransaction tr);
      int same = 1; // Suppose that are same
      if (localAddr != tr.localAddr) same = 0;
      if (globalAddr != tr.globalAddr) same = 0;
      if (tag != tr.tag) same = 0;
      if (length != tr.length) same = 0;
      if (transType != tr.transType) same = 0;
      for (integer i=0; i < data.size; i++)
        if (data[i] != tr.data[i]) same=0;
      compare = same;
    endfunction : compare

    //-- Show transaction -----------------------------------------------------
    // Function show transaction in text format
    function void display(integer full=0);
      int aux;
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
        RDCL:
         $write("RDCL\n");
      endcase;

      // Write also data for specified transaction types
      aux = (length == 0)? 4096 : length;      
      if (full && (transType == L2LW || transType == L2GW || transType == RDC
          || transType == RDCL) )
      for (integer i=0; i < aux; i=i+8)
        for (integer j = i+7; j >= i; j--) begin
          if (j==i+7)
            $write("DATA: 0x");
          if (j < aux)
            $write("%x", data[j]);
          else
            $write("00");
          if (j == i)
            $write("\n");
      end
    endfunction

    // -- Private Class Methods --

    //-- Randomize data ------------------------------------------------------- 
    // This function is called after randomize function
    function void post_randomize();
      // Randomize data
      case (transType)
        L2LW, RDC, RDCL, L2GW : begin
          data             = new[length];
          for (integer i=0; i < data.size; i++)
            data[i] = $urandom_range(0,255);
          end
      endcase;
        
      // Null unusefull bytes
      case (transType)
         L2LW, L2LR, RDC, RDCL :
            globalAddr[63:32] = 32'h00000000;
      endcase;

      case (transType)
         L2LW, L2GW :
            tag = 8'h00;
      endcase;      
               
      if ( !enTxDelay )
        txDelay = 0;
     endfunction : post_randomize

    //-- Copy Data ------------------------------------------------------------ 
    // Function copy data from actual object to copy object
    virtual function void copyData(InternalBusTransaction copy);
      copy.localAddr   = localAddr;
      copy.globalAddr  = globalAddr;
      copy.tag         = tag;
      copy.length      = length;
      copy.transType   = transType;
      copy.data        = new[data.size];
      
      for (integer i=0; i < data.size; i++)
        copy.data[i]   = data[i];

      copy.txDelay         = txDelay;
      copy.enTxDelay       = enTxDelay;
      copy.enInsideTxDelay = enInsideTxDelay;
    
    
      copy.L2LW_wt = L2LW_wt;
      copy.L2LR_wt = L2LR_wt;
      copy.L2GW_wt = L2GW_wt;
      copy.G2LR_wt = G2LR_wt;
      copy.RDC_wt  = RDC_wt;
      copy.RDCL_wt = RDCL_wt;

      copy.txDelayEn_wt             = txDelayEn_wt; 
      copy.txDelayDisable_wt        = txDelayDisable_wt;
      copy.insideTxDelayEn_wt       = insideTxDelayEn_wt; 
      copy.insideTxDelayDisable_wt  = insideTxDelayDisable_wt;

      copy.txDelayLow          = txDelayLow;
      copy.txDelayHigh         = txDelayHigh;
      copy.insideTxDelay       = insideTxDelay; 
    
      copy.localAddrLow   = localAddrLow;
      copy.localAddrHigh  = localAddrHigh;
      copy.globalAddrLow  = globalAddrLow;
      copy.globalAddrHigh = globalAddrHigh;
      copy.tagLow         = tagLow;
      copy.tagHigh        = tagHigh;
      copy.lengthLow      = lengthLow;
      copy.lengthHigh     = lengthHigh;
    endfunction : copyData
  
  endclass : InternalBusTransaction


  // -- Trnsaction mailbox ----------------------------------------------------
  typedef mailbox #(InternalBusTransaction) tTransMbx;

endpackage : ib_transaction_pkg



