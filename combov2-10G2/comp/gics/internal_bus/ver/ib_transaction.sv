/*
 * ib_transaction.sv: Internal Bus Transaction
 * Copyright (C) 2009 CESNET
 * Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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
 * $Id: ib_transaction.sv 8517 2009-05-28 10:55:58Z washek $
 *
 * TODO:
 *
 */


// -- Internal Bus Transaction Types Constants --------------------------------
const logic [3:0] L2LR_TYPE = 4'b0000; // Local to Local Read
const logic [3:0] L2LW_TYPE = 4'b0001; // Local to Local Write
const logic [3:0] G2LR_TYPE = 4'b0010; // Global to Local Read
const logic [3:0] L2GW_TYPE = 4'b0011; // Local to Global Write
const logic [3:0] RDC_TYPE  = 4'b0101; // Read completition (not last packet)
const logic [3:0] RDCL_TYPE = 4'b1101; // Read completition (last packet)

// -- Internal Bus Transaction Types ------------------------------------------
typedef enum {L2LR=0, L2LW=1, G2LR=2, L2GW=3, RDC=5, RDCL=13} eTransactionType;

// ----------------------------------------------------------------------------
// -- Internal Bus Transaction Class
// ----------------------------------------------------------------------------
/* This class describe transaction and simplify transaction random generation.
 * generation.
 */
class InternalBusTransaction extends Transaction;

  rand logic [31:0]   localAddr;  // Transaction Local Address
  rand logic [63:0]   globalAddr; // Transaction Global Address
  rand logic [7:0]    tag;        // Transaction Tag
  rand logic [12:0]   length;     // Transaction Length
  rand logic [3:0]    transType;  // Transaction Type
  logic [7:0] data[];             // Transaction Data
  
  // Parameters (type probabilities and rand variables limits)
  pIbTransaction P;
  
  //number of less significant bits of addresses that are set to zero
  int addrAlignBits = 0;
  

  // -- Constraints --
  
  constraint cType {
    transType dist { L2LW := P.L2LW_WT, L2LR := P.L2LR_WT,
                     L2GW := P.L2GW_WT, G2LR := P.G2LR_WT,
                     RDC  := P.RDC_WT,  RDCL := P.RDCL_WT};
  }
  
  constraint cAddr {
    localAddr  inside {[P.localAddrLow:P.localAddrHigh]};
    globalAddr inside {[P.globalAddrLow:P.globalAddrHigh]};
    
    // Transaction can't cross 4kB
    globalAddr[11:0] + length <= 13'h1000;
    localAddr[11:0]  + length <= 13'h1000;
    solve length before globalAddr;
    solve length before localAddr;
  }
  
  constraint cAddrAlign {
    if (addrAlignBits > 0)
      globalAddr[0] == 0 && localAddr[0] == 0;
    if (addrAlignBits > 1) 
      globalAddr[1] == 0 && localAddr[1] == 0;
    if (addrAlignBits > 2)
      globalAddr[2] == 0 && localAddr[2] == 0;
    if (addrAlignBits > 3)
      globalAddr[3] == 0 && localAddr[3] == 0;
  }
  
  constraint cTag {
    tag inside {[P.tagLow:P.tagHigh]};
  }
  
  constraint cLength {
    length <= 13'h1000;
    length >  13'h0000;
    
    length inside {[P.lengthLow : P.lengthHigh]};
    
    length dist {[0:16]  :/ 10,
                 [17:13'h0FFE] :/ 10,
                 13'h0FFF := 1,
                 13'h1000 := 3
                };
  }
  
  // -- Public Class Methods --

  //-- Constructor ------------------------------------------------------------
  function new(pIbTransaction params = dIbTransaction, int addrAlignBits = 0);
    P = params;
    this.addrAlignBits = addrAlignBits;
  endfunction : new
  
  //-- Copy -------------------------------------------------------------------
  // Copy constructor
  virtual function Transaction copy(Transaction to = null);
    InternalBusTransaction tr;
    if (to)
      $cast(tr, to);
    else
      tr = new;
  
    tr.localAddr   = localAddr;
    tr.globalAddr  = globalAddr;
    tr.tag         = tag;
    tr.length      = length;
    tr.transType   = transType;
    tr.data        = new[data.size];
    
    for (int i=0; i < data.size; i++)
      tr.data[i]   = data[i];

    tr.P = P;
    
    tr.addrAlignBits  = addrAlignBits;
    
    copy = tr;
  endfunction: copy
  
  
  //-- Compare ----------------------------------------------------------------
  // Compare transaction with another. Return 1 for same transactions
  // diff strnig not implemented
  // kind=1 - compare data
  virtual function bit compare(input Transaction to, 
                                     output string diff, input int kind = -1);
    InternalBusTransaction tr;
    int same = 1; // Suppose that are same
    $cast(tr, to);
    
    if (localAddr != tr.localAddr) same = 0;
    if (globalAddr != tr.globalAddr) same = 0;
    if (tag != tr.tag) same = 0;
    if (length != tr.length) same = 0;
    if (transType != tr.transType) same = 0;
    if (kind == 1 && same == 1 && data != tr.data) same = 0;
    compare = same;
  endfunction : compare

  //-- Show transaction -------------------------------------------------------
  // Function show transaction in text format
  virtual function void display(string prefix = "");
    bit dots_written = 0;
    
    if (prefix != "") begin
      $write("---------------------------------------------------------\n");
      $write("-- %s\n",prefix);
      $write("---------------------------------------------------------\n");
    end
     
    $write("Transaction LOCAL_ADDR=%0x, GLOBAL_ADDR=%0x",localAddr,globalAddr);
    $write(", TAG=%0x, LENGTH=%0x, TYPE=", tag, length);
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
      default:
        $write("unknown\n");
    endcase;

    // Write also data for specified transaction types
    if (transType == L2LW || transType == L2GW || transType == RDC
        || transType == RDCL)
      for (int i=0; i < data.size; i=i+8) begin
        if (i > 8 && i < data.size - 16) begin
          if (dots_written == 0)
            $write("DATA: ...\n");
          dots_written = 1;
        end
        else begin
          $write("DATA: 0x");
          for (int j=i+7; j >= i; j--) begin
            if (j < data.size)
              $write("%2x", data[j]);
            else
              $write("00");
            if (j == i)
              $write("\n");
          end
        end
      end
  
  endfunction

  
  //-- Have data --------------------------------------------------------------
  // Returns 1 if tansaction have data (types L2LW, L2GW, RDC, RDCL).
  // Otherwise it returns 0.
  function bit haveData();
    if (transType inside {L2LW, L2GW, RDC, RDCL})
      haveData = 1;
    else
      haveData = 0;
  endfunction
  
  
  // -- Private Class Methods --

  //-- Randomize data ---------------------------------------------------------
  // This function is called after randomize function
  function void post_randomize();
    
    // Null unuseful bytes
    if (transType inside {L2LW, L2LR, RDC, RDCL})
      globalAddr[63:32] = 32'h00000000;
    
    // Randomize data
    if (transType inside {L2LW, L2GW, RDC, RDCL}) begin
      data = new[length];
      for (int i=0; i < data.size; i++)
        data[i] = $urandom_range(0,255);
    end
    
  endfunction : post_randomize
   
endclass : InternalBusTransaction


// -- Trnsaction mailbox ------------------------------------------------------
typedef mailbox #(InternalBusTransaction) tTransMbx;

