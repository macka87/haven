//
// ib_transaction.sv: Internal Bus Transaction
// Copyright (C) 2007 CESNET
// Author(s): Petr Kobierský <kobiersky@liberouter.org>
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in
//    the documentation and/or other materials provided with the
//    distribution.
// 3. Neither the name of the Company nor the names of its contributors
//    may be used to endorse or promote products derived from this
//    software without specific prior written permission.
//
// This software is provided ``as is'', and any express or implied
// warranties, including, but not limited to, the implied warranties of
// merchantability and fitness for a particular purpose are disclaimed.
// In no event shall the company or contributors be liable for any
// direct, indirect, incidental, special, exemplary, or consequential
// damages (including, but not limited to, procurement of substitute
// goods or services; loss of use, data, or profits; or business
// interruption) however caused and on any theory of liability, whether
// in contract, strict liability, or tort (including negligence or
// otherwise) arising in any way out of the use of this software, even
// if advised of the possibility of such damage.
//
// $Id: ib_transaction.sv 4766 2008-08-13 20:48:03Z xkobie00 $
//

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
 
  // -- Internal Bus Compare type constants ----------------------------------
  const int CMP_PCIE2IB_RD_WR = 1;
  const int CMP_PCIE2IB_CMPL  = 2;

  // -- Internal Bus Transaction Types Constants ------------------------------
  const logic [3:0] L2LW_TYPE = 4'b0000; // Local to Local Write
  const logic [3:0] L2LR_TYPE = 4'b0001; // Local to Local Read
  const logic [3:0] L2GW_TYPE = 4'b0010; // Local to Global Write
  const logic [3:0] G2LR_TYPE = 4'b0011; // Global to Local Read
  const logic [3:0] RDC_TYPE  = 4'b0101; // Read completition (not last packet)
  const logic [3:0] RDCL_TYPE = 4'b1101; // Read completition (last packet)

  // -- Internal Bus Transaction Types ----------------------------------------
  typedef enum {L2LW=0, L2LR=1, L2GW=2, G2LR=3, RDC=5, RDCL=13} eTransactionType;

  // --------------------------------------------------------------------------
  // -- Internal Bus Transaction Class
  // --------------------------------------------------------------------------
  /* This class describe transaction and simplyfy transaction random
   * generation.
   */
  class InternalBusTransaction extends Transaction;

    // -- Public Class Atributes --
    rand logic [31:0]     localAddr;  // Transaction Local Address
    rand logic [63:0]     globalAddr; // Transaction Global Address
    rand logic [15:0]     tag;        // Transaction Tag
    rand logic [11:0]     length;     // Transaction Length
    rand eTransactionType transType;  // Transaction Type
    logic [7:0] data[];               // Transaction Data
    
    // Transaction types probability weights (set 0 to switch off)
    int L2LW_wt = 0; // Local to Local Write
    int L2LR_wt = 0; // Local to Local Read
    int L2GW_wt = 0; // Local to Global Write
    int G2LR_wt = 1; // Global to Local Read
    int RDC_wt  = 0; // Read completition (not last packet)
    int RDCL_wt = 0; // Read completition (last packet)

    // Transaction parameter limits
    logic [31:0] localAddrLow   = 32'h00000000;
    logic [31:0] localAddrHigh  = 32'h000FFFFF;
    logic [63:0] globalAddrLow  = 64'h000000000000000;
    logic [63:0] globalAddrHigh = 64'h0000001FFFFFFFF;
    logic [15:0] tagLow         = 16'h0000;
    logic [15:0] tagHigh        = 16'h00FF;
    logic [11:0] lengthLow      = 12'h000;
    logic [11:0] lengthHigh     = 12'h0FF;

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

    // -- Public Class Methods --
  

    //-- Copy ----------------------------------------------------------------- 
    // Copy constructor
       virtual function Transaction copy(Transaction to = null);
       InternalBusTransaction tr;
       if (to == null)
         tr = new();
       else 
         $cast(tr, to);
       copyData(tr);
       copy = tr;
    endfunction : copy


     //-- Compare -------------------------------------------------------------- 
     // Compare transaction with another. Return 1 for same transactions
     virtual function bit compare(input Transaction to, output string diff, input int kind = -1);
       int same = 1; // Suppose that are same
       InternalBusTransaction tr;
       $cast(tr, to);

       // Compare for PCIE2IB
       if (kind == CMP_PCIE2IB_RD_WR) begin
         if (transType  != tr.transType)  same = 0;   
         if (localAddr  != tr.localAddr)  same = 0;
         if (globalAddr != tr.globalAddr) same = 0;
         if (length     != tr.length)     same = 0;
         for (integer i=0; i < data.size; i++)
           if (data[i] != tr.data[i]) same=0;
       end
       else if (kind == CMP_PCIE2IB_CMPL) begin
         if (transType  != tr.transType)  same = 0;   
         if (localAddr  != tr.localAddr)  same = 0;
         if (length     != tr.length)     same = 0;
         for (integer i=0; i < data.size; i++)
           if (data[i] != tr.data[i]) same=0;
       end
       // Default compare
       else begin
         if (transType != tr.transType) same = 0;      
         if (localAddr != tr.localAddr) same = 0;
         if (globalAddr != tr.globalAddr) same = 0;
         if (length != tr.length) same = 0;

         if (transType == RDCL)
           if (tag != tr.tag) same = 0;      
         for (integer i=0; i < data.size; i++)
           if (data[i] != tr.data[i]) same=0;
       end;

      compare = same;
    endfunction : compare

    //-- Show transaction -----------------------------------------------------
    // Function show transaction in text format
    function void display(string prefix = ""); 
      $write("Transaction LOCAL_ADDR=%0x, GLOBAL_ADDR=%0x, TAG=%0x, LENGTH=%0x, TYPE=", localAddr, globalAddr, tag, length);
      case (transType)
        L2LW: $write("L2LW\n");
        L2LR: $write("L2LR\n");
        L2GW: $write("L2GW\n");
        G2LR: $write("G2LR\n");
        RDC:  $write("RDC\n");
        RDCL: $write("RDCL\n");
      endcase;

      // Write also data for specified transaction types
      if (transType != L2LR && transType != G2LR)
        for (integer i=0; i < data.size; i=i+8)
          for (integer j = i+7; j >= i; j--) begin
            if (j==i+7) $write("DATA: 0x");
            if (j < data.size)
              $write("%x", data[j]);
            else
              $write("XX");
            if (j == i) $write("\n");
           end
      $write("\n");
    endfunction

    // -- Private Class Methods --

    //-- Randomize data ------------------------------------------------------- 
    // This function is called after randomize function
    function void post_randomize();
      logic [11:0] addr;
      int len;

      // TEMPORARY alignment (Remove when read align circuit)
      if (transType == G2LR) begin
         localAddr[2:0] = 3'b000; //TODO TODO TODO
         globalAddr[2:0] = 3'b000;
         end

      // 4096 B address alignment (Neprekroci stranku)
      addr = (transType == RDCL) ? localAddr[11:0] : globalAddr[11:0];
      len  = (length == 0) ? 4096 : length;
      if ((addr + len) > 4096) length = 4096 - addr;
       
      // Randomize data
      case (transType)
        L2LW, RDC, RDCL, L2GW : begin           
          len  = (length == 0) ? 4096 : length;
          data    = new[len];
          for (integer i=0; i < data.size; i++)
            data[i] = $urandom_range(0,255);
          end
      endcase;
        
      // Null unusefull bytes
      case (transType)
         L2LW, L2LR, RDC, RDCL :
            globalAddr[63:32] = 32'h00000000;
      endcase;
               
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

      
      copy.L2LW_wt = L2LW_wt;
      copy.L2LR_wt = L2LR_wt;
      copy.L2GW_wt = L2GW_wt;
      copy.G2LR_wt = G2LR_wt;
      copy.RDC_wt  = RDC_wt;
      copy.RDCL_wt = RDCL_wt;


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

