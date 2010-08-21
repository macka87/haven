//
// pcie_transaction_pkg.sv: PCI Express Transaction
// Copyright (C) 2007 CESNET
// Author(s): Tomas Malek <tomalek@liberouter.org>
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
// $Id: pcie_transaction.sv 4766 2008-08-13 20:48:03Z xkobie00 $
//
 
  // -- Compare type constants ----------------------------------
  const int CMP_IB2PCIE_RD_WR = 1;
  const int CMP_IB2PCIE_CMPL  = 2;


  // -- Format Constants
  const logic [1:0] FMT_3DWH_ND = 2'b00;     
  const logic [1:0] FMT_4DWH_ND = 2'b01;     
  const logic [1:0] FMT_3DWH_WD = 2'b10;     
  const logic [1:0] FMT_4DWH_WD = 2'b11;     
 
  // -- Type Constants
  const logic [4:0] TYPE_MEM = 5'b00000;
  const logic [4:0] TYPE_CPL = 5'b01010;

  // -- Command Constants
  const logic [6:0] CMD_RD32 = {FMT_3DWH_ND, TYPE_MEM};
  const logic [6:0] CMD_RD64 = {FMT_4DWH_ND, TYPE_MEM};
  const logic [6:0] CMD_WR32 = {FMT_3DWH_WD, TYPE_MEM};
  const logic [6:0] CMD_WR64 = {FMT_4DWH_WD, TYPE_MEM};
  const logic [6:0] CMD_CPLD = {FMT_3DWH_WD, TYPE_CPL};

  // -- Pcie Transaction Types
  typedef enum {RD32 = 0, RD64 = 1,
                WR32 = 2, WR64 = 3,
                CPLD = 4, CPLD_LAST = 5} ePcieTransactionType;

  // -- Completion status constants
  const logic [2:0] C_CPLSTAT_OK = 3'b000;

  // -- Completion  Types
  typedef enum {CPLSTAT_OK = 0} eCplStatus;
  
  // -- BAR hit types
  typedef enum {B1111110 = 126, B1111101 = 125, B1111011 = 123,
                B1110111 = 119, B1101111 = 111, B1011111 =  95, 
                B0111111 =  63 } eBarHitType;  

  // -- Byte enables  Types
  typedef enum {F1111 = 32'h000F, F1110 = 32'h000E, F1100 = 32'h000C, 
                F1000 = 32'h0008, F0111 = 32'h0007, F0011 = 32'h0003, 
                F0110 = 32'h0006, F0100 = 32'h0004, F0010 = 32'h0002, 
                F0001 = 32'h0001 } eFirstEnable;

  typedef enum {L1111 = 32'h000F, L0111 = 32'h0007, 
                L0011 = 32'h0003, L0001 = 32'h0001, L0000 = 32'h0000} eLastEnable;


  // --------------------------------------------------------------------------
  // -- PCI Express Transaction Class
  // --------------------------------------------------------------------------
  /* This class describe transaction and simplyfy transaction random
   * generation.
   */
  class PcieTransaction extends Transaction;

    // -- Public Class Atributes --
    rand eBarHitType          barHitN;          // BAR hit
    rand ePcieTransactionType transType;        // Transaction Type
    rand logic [2:0]          tc;               // Trafic class
    logic                     td      = 1'b0;   // TLP digest presence
    logic                     ep      = 1'b0;   // TLP poisoning indication
    logic [1:0]               attr    = 2'b00;  // Attributes
    rand logic [9:0]          length;           // Transaction Length
    rand logic [63:0]         address;          // Address
    rand logic [ 6:0]         lowerAddr;        // Lower address
    rand logic [15:0]         requesterId;      // RequesterID
    rand logic [15:0]         completerId;      // CompleterID
    rand logic [3:0]          lastBE;           // last data word byte enables       
    rand logic [3:0]          firstBE;          // first data word byte enables       
    rand logic [7:0]          tag;              // Transaction tag
    rand eCplStatus           cplStatus;        // Completion status
    rand logic [11:0]         byteCount;        // Byte count    
    logic                     bcm      = 1'b0;  // PCIE completer must not set
    logic [7:0] data[];                         // Transaction Data

    rand bit                  supported;        // Supported/Unsupported transaction
    rand bit                  error;            // Transaction with error //TODO


    // Transaction types probability weights (set 0 to switch off)
    int RD32_wt = 0; 
    int RD64_wt = 0; 
    int WR32_wt = 0; 
    int WR64_wt = 0; 
    int CPLD_wt = 0; // always, no sense to generated CPLD transaction
    int CPLD_LAST_wt = 0;

    // Supported/unsupported transaction probabality weights
    int SUPPORTED_wt   = 50;
    int UNSUPPORTED_wt =  0; // TODO

    // Error/ OK transaction
    int ERROR_wt   = 50;
    int NOERROR_wt =  0; // TODO
       
    // Transaction parameter limits
    int maxReadRequestSize      = 4096;     
    int maxPayloadSize          = 4096;

    logic [ 6:0] lowerAddrLow   =  7'b0000000;
    logic [ 6:0] lowerAddrHigh  =  7'b1111111;
    logic [63:0] addressLow     = 64'h000000000000000;
    logic [63:0] addressHigh    = 64'hFFFFFFFFFFFFFFF;
    logic [ 7:0] tagLow         =  8'b00000000;
    logic [ 7:0] tagHigh        =  8'b11111111;
    logic [ 2:0] tcLow          =  3'b000;
    logic [ 2:0] tcHigh         =  3'b111;    
    logic [ 9:0] lengthLow      = 10'b0000000000;
    logic [ 9:0] lengthHigh     = 10'b0000001111;

    // -- Private Class Atributes --
    
    // -- Constrains --

    // Constrain for Transactions Types
    constraint cTransactions {
      transType dist { RD32 := RD32_wt, RD64 := RD64_wt,
                       WR32 := WR32_wt, WR64 := WR64_wt,
                       CPLD := CPLD_wt, CPLD_LAST := CPLD_LAST_wt};
    }

    // Constrain for Supported/Unsupported Transactions
    constraint cSupportedError {
      supported dist { 1'b1 := SUPPORTED_wt,
                       1'b0 := UNSUPPORTED_wt};
      error     dist { 1'b1 := ERROR_wt,
                       1'b0 := NOERROR_wt};
    }    

    // Constrain for Data ranges
    constraint cRanges {
      lowerAddr  inside {[lowerAddrLow:lowerAddrHigh]};
      address    inside {[addressLow:addressHigh]};
      tag        inside {[tagLow:tagHigh]};
      length     inside {[lengthLow:lengthHigh]};
      tc         inside {[tcLow:tcHigh]};
      address[1:0]   == 2'b00;
      lowerAddr[1:0] == 2'b00; // TODO TODO TODO TODO REMOVE When realign is finished 
      transType == RD32 || transType == WR32 -> address[63:32] == 32'h00000000;
    }

    // Constrains for byte enables
    constraint cFirstEnables {
      length == 1 -> firstBE dist {F1111 := 1, F1110 := 1, F1100 := 1, F1000 := 1, F0111 := 1,
                                   F0011 := 1, F0110 := 1, F0100 := 1, F0010 := 1, F0001 := 1};
      length != 1 -> firstBE dist {F1111 := 1, F1110 := 1, F1100 := 1, F1000 := 1, F0111 := 0,
                                   F0011 := 0, F0110 := 0, F0100 := 0, F0010 := 0, F0001 := 0};
    }

    constraint cLastEnables {
      length == 1 -> lastBE dist {L1111 := 0, L0111 := 0, L0011 := 0, L0001 := 0, L0000 := 1};
      length != 1 -> lastBE dist {L1111 := 1, L0111 := 1, L0011 := 1, L0001 := 1, L0000 := 0};

    }


    // -- Public Class Methods --

    //-- Copy ----------------------------------------------------------------- 
    // Copy constructor
       virtual function Transaction copy(Transaction to = null);
       PcieTransaction tr;
       if (to == null)
         tr = new();
       else 
         $cast(tr, to);
       copyData(tr);
       copy = tr;
    endfunction : copy

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
     virtual function bit compare(input Transaction to, output string diff, input int kind = -1);

       int same = 1; // Suppose that are same
       PcieTransaction tr;
       $cast(tr, to);

       // Compare for IB2PCIE
       if (kind ==  CMP_IB2PCIE_RD_WR) begin
         if (transType != tr.transType) same = 0; 
         if (tc != tr.tc) same = 0;
         if (td != tr.td) same = 0;
         if (ep != tr.ep) same = 0;
         if (attr != tr.attr) same = 0;
         if (length != tr.length) same = 0;
         if (requesterId != tr.requesterId) same = 0;
         if (firstBE != tr.firstBE) same = 0;
         if (lastBE != tr.lastBE) same = 0;
         if (address != tr.address) same = 0;
         for (integer i=0; i < data.size; i++)
           if (data[i] != tr.data[i]) same=0;
       end
       else if (kind == CMP_IB2PCIE_CMPL) begin
         if (transType != tr.transType) same = 0; 
         if (tc != tr.tc) same = 0;
         if (td != tr.td) same = 0;
         if (ep != tr.ep) same = 0;
         if (attr != tr.attr) same = 0;
         if (length != tr.length) same = 0;
         if (completerId != tr.completerId) same = 0;
         if (cplStatus != tr.cplStatus) same = 0;
         if (bcm != tr.bcm) same = 0;
         if (byteCount != tr.byteCount) same = 0;
         if (lowerAddr != tr.lowerAddr) same = 0;
       end

      compare = same;
    endfunction : compare

   //-- Show transaction -----------------------------------------------------
    // Function show transaction in text format
    function void display(string prefix = "");

      if (supported)
        $write("Transaction: TYPE=");   
      else
        $write("Unsupported: TYPE=");    
        
      case (transType)
        RD32: $write("RD32,");
        RD64: $write("RD64,");
        WR32: $write("WR32,");
        WR64: $write("WR64,");
        CPLD: $write("CPLD,");
        CPLD_LAST: $write("CPLD_LAST,");
      endcase;

      $write("BARHIT_N=%s,",barHitN);
      $write("TC=%0x,",tc);
      $write("TD=%0x,",td);
      $write("EP=%0x,",ep);
      $write("ATTR=%0x,",attr);
      $write("LENGTH=%0x,",length);

      case (transType)
        RD32,RD64,WR32,WR64: begin
          $write("REQUESTER_ID=%0x,", requesterId);
          $write("TAG=%0x,",tag);
          $write("lastBE=%0x,",lastBE);
          $write("firstBE=%0x,",firstBE);
          $write("ADDR=%0x,",address);
          $write("\n");
          end
        CPLD, CPLD_LAST: begin
          $write("COMPLETER_ID=%0x,", completerId);
          $write("CPLSTAT=%0x,",cplStatus);
          $write("BCM=%0x\n",bcm);
          $write("BYTECOUNT=%0x,",byteCount);
          $write("REQUESTER_ID=%0x,", requesterId);
          $write("TAG=%0x,",tag);
          $write("LOWERADDR=%0x,",lowerAddr);
          $write("\n");
          end
      endcase;

      // Write also data for specified transaction types
      if ((transType == CPLD ||transType == CPLD_LAST || transType == WR32 || transType == WR64) )
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
      // treat length 0 as 1024 
      int length_10_0 = (length == 0) ? 1024 : length;
       
      // Fix Requests Limits
      if ((transType == RD32 || transType == RD64) && (length_10_0 > maxReadRequestSize/4)) begin
        length_10_0 = maxReadRequestSize/4;
        length      = maxReadRequestSize/4;
      end
      if ((transType != RD32 && transType != RD64) && (length_10_0 > maxPayloadSize/4)) begin
        length_10_0 = maxPayloadSize/4;
        length      = maxPayloadSize/4;
        end

      // Randomize data
      case (transType)
        WR32, WR64: 
        begin
          data = new[length_10_0*4 - minusBE()];                          
          for (integer i=0; i < data.size; i++)
            data[i] = $urandom_range(0,255);
        end
        CPLD, CPLD_LAST:
        begin
          data = new[length_10_0*4 - lowerAddr[1:0]];                          
          for (integer i=0; i < data.size; i++)
            data[i] = $urandom_range(0,255);
        end
      endcase;

      // Set correct byte count for Last Completition
      if (transType == CPLD_LAST)
        byteCount = length_10_0*4 - lowerAddr[1:0];
                                                               
     endfunction : post_randomize

    //-- Copy Data ------------------------------------------------------------ 
    // Function copy data from actual object to copy object
    virtual function void copyData(PcieTransaction copy);

      copy.transType = transType;  
      copy.tc = tc;         
      copy.td = td;         
      copy.ep = ep;         
      copy.attr = attr;       
      copy.length = length;     
      copy.address = address;    
      copy.lowerAddr = lowerAddr; 
      copy.maxReadRequestSize = maxReadRequestSize;
      copy.maxPayloadSize = maxPayloadSize;
      copy.error = error;

      copy.requesterId = requesterId;
      copy.completerId = completerId;
      copy.lastBE = lastBE;     
      copy.firstBE = firstBE;    
      copy.tag = tag;        
      copy.cplStatus = cplStatus;  
      copy.byteCount = byteCount;  
      copy.bcm = bcm;  
      copy.barHitN = barHitN;
      copy.supported = supported;
      copy.data = new[data.size];
      
      for (integer i=0; i < data.size; i++)
        copy.data[i]   = data[i];

      copy.RD32_wt = RD32_wt; 
      copy.RD64_wt = RD64_wt; 
      copy.WR32_wt = WR32_wt; 
      copy.WR64_wt = WR64_wt; 
      copy.CPLD_wt = CPLD_wt; 
   
      copy.lowerAddrLow   = lowerAddrLow;
      copy.lowerAddrHigh  = lowerAddrHigh;
      copy.addressLow     = addressLow;
      copy.addressHigh    = addressHigh;
      copy.tagLow         = tagLow;
      copy.tagHigh        = tagHigh;
      copy.lengthLow      = lengthLow;
      copy.lengthHigh     = lengthHigh;
      copy.tcLow          = tcLow;
      copy.tcHigh         = tcHigh;      

    endfunction : copyData  

    // -- minus BE ------------------------------------------------------------
    // Count how is length in byte shortened
    function integer minusBE();
      int first;
      int last;
      case (firstBE)
        F1111: first = 0;
        F1110: first = 1;
        F1100: first = 2;
        F1000: first = 3;           
        F0111: first = 1; 
        F0011: first = 2; 
        F0110: first = 2; 
        F0100: first = 3; 
        F0010: first = 3; 
        F0001: first = 3; 
      endcase       
      case (lastBE)
        L1111: last  = 0;
        L0111: last  = 1;
        L0011: last  = 2;
        L0001: last  = 3;
        L0000: last  = 0;
      endcase;
      minusBE = last + first;     
    endfunction : minusBE

  endclass : PcieTransaction

