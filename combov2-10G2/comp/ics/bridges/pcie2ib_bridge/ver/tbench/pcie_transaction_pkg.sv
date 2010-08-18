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
// $Id: pcie_transaction_pkg.sv 2981 2008-06-30 09:16:01Z tomalek $
//

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package pcie_transaction_pkg; 
  
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
                CPLD = 4} ePcieTransactionType;

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
  class PcieTransaction;

    // -- Public Class Atributes --
    rand ePcieTransactionType transType;  // Transaction Type
    rand logic [2:0]          tc;         // Trafic class
    rand logic                td;         // TLP digest presence
    rand logic                ep;         // TLP poisoning indication
    rand logic [1:0]          attr;       // Attributes
    rand logic [9:0]          length;     // Transaction Length

    rand logic [63:0]         address;    // Address
    rand logic [ 6:0]         lowerAddr;  // Lower address

    rand logic [ 7:0]         busnum_req; // Requester bus number
    rand logic [ 4:0]         devnum_req; // Requester device number
    rand logic [ 2:0]         funcnum_req;// Requester function number
    rand logic [ 7:0]         busnum_cpl; // Completer bus number
    rand logic [ 4:0]         devnum_cpl; // Completer device number
    rand logic [ 2:0]         funcnum_cpl;// Completer function number

    rand logic [3:0]          lastBE;     // last data word byte enables       
    rand logic [3:0]          firstBE;    // first data word byte enables       
    rand logic [7:0]          tag;        // Transaction tag

    rand eCplStatus           cplStatus;  // Completion status                
    rand logic [11:0]         byteCount;  // Byte count    
    rand logic                bcm;        // PCIE completer must not set

    rand eBarHitType          barHitN;    // BAR hit

    rand bit                  supported;  // Supported/Unsupported transaction

    logic [7:0] data[];                   // Transaction Data

    // Delay attributes
    rand bit enTxDelay;           // Enable Tx Delay
    rand bit enInsideTxDelay;     // Enable Inside Tx Delay
    rand integer txDelay;         // Wait txDelay clock cycles before sending
    
    // Transaction types probability weights (set 0 to switch off)
    int RD32_wt = 0; 
    int RD64_wt = 0; 
    int WR32_wt = 1; 
    int WR64_wt = 1; 
    int CPLD_wt = 0; // always, no sense to generated CPLD transaction

    // Supported/unsupported transaction probabality weights
    int SUPPORTED_wt   = 50;
    int UNSUPPORTED_wt =  1;

    // Delay weights
    int txDelayEn_wt             = 1; 
    int txDelayDisable_wt        = 5;
    int insideTxDelayEn_wt       = 1; 
    int insideTxDelayDisable_wt  = 5;

    // Byte enables weights
    int F1111_wt = 1; 
    int F1110_wt = 1; 
    int F1100_wt = 1; 
    int F1000_wt = 1;
    int F0111_wt = 0; 
    int F0011_wt = 0; 
    int F0110_wt = 0; 
    int F0100_wt = 0; 
    int F0010_wt = 0; 
    int F0001_wt = 0; 
    
    int L1111_wt = 1; 
    int L0111_wt = 1; 
    int L0011_wt = 1; 
    int L0001_wt = 1;
    int L0000_wt = 0;

    // Bar Hit weights
    int B1111110_wt = 1;
    int B1111101_wt = 1;
    int B1111011_wt = 1;
    int B1110111_wt = 1;
    int B1101111_wt = 1;
    int B1011111_wt = 1; 
    int B0111111_wt = 1;
                
    // Transaction parameter limits
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

    // Delays limits
    int txDelayLow          = 0;
    int txDelayHigh         = 3;
    int insideTxDelay       = 3; // Maximal delay between transaction words


    // -- Private Class Atributes --
    
    // -- Constrains --

    // Constrain for Transactions Types
    constraint cTransactions {
      transType dist { RD32 := RD32_wt,RD64 := RD64_wt,
                       WR32 := WR32_wt,WR64 := WR64_wt, CPLD := CPLD_wt};
    }

    // Constrain for Supported/Unsupported Transactions
    constraint cSupported {
      supported dist { 1'b1 := SUPPORTED_wt,
                       1'b0 := UNSUPPORTED_wt};
    }    

    // Constrain for Data ranges
    constraint cRanges {
      lowerAddr  inside {[lowerAddrLow:lowerAddrHigh]};
      address    inside {[addressLow:addressHigh]};
      tag        inside {[tagLow:tagHigh]};
      length     inside {[lengthLow:lengthHigh]};
      tc         inside {[tcLow:tcHigh]};
    }

    // Delays constrains
    constraint cDelays {
      txDelay inside {[txDelayLow:txDelayHigh]};
      enTxDelay dist { 1'b1 := txDelayEn_wt,
                       1'b0 := txDelayDisable_wt};
      enInsideTxDelay dist { 1'b1 := insideTxDelayEn_wt,
                             1'b0 := insideTxDelayDisable_wt};
    }

    // Constrains for byte enables
    constraint cFirstEnables {
      firstBE dist {F1111 := F1111_wt, F1110 := F1110_wt, F1100 := F1100_wt, F1000 := F1000_wt,
                    F0111 := F0111_wt, F0011 := F0011_wt, F0110 := F0110_wt, F0100 := F0100_wt, 
                    F0010 := F0010_wt, F0001 := F0001_wt };
    }

    constraint cLastEnables {
      lastBE dist {L1111 := L1111_wt, L0111 := L0111_wt, 
                   L0011 := L0011_wt, L0001 := L0001_wt, L0000 := L0000_wt};
    }
    
    // Constrains for bar hit    
    constraint  cBarHit{
      barHitN dist {B1111110 := B1111110_wt, B1111101 := B1111101_wt, B1111011 := B1111011_wt,
                    B1110111 := B1110111_wt, B1101111 := B1101111_wt, B1011111 := B1011111_wt,
                    B0111111 := B0111111_wt};
    }

    // Constraints for others 
    constraint cOthers {
      td dist   { 1'b1 := 0,                 // Digest is not generated by PCIe core
                  1'b0 := 1};
      ep dist   { 1'b1 := 0,                 // no support for poisoning so far
                  1'b0 := 1};
      bcm dist  { 1'b1 := 0,                 // set only on PCI-X
                  1'b0 := 1};
      attr dist { 2'b00 := 1, 2'b01 := 1,    // no support for poisoning so far
                  2'b10 := 1, 2'b11 := 1};
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
    virtual function PcieTransaction copy();
       copy = new;
       copyData(copy);
    endfunction : copy

     //-- Compare -------------------------------------------------------------- 
    // Compare transaction with another. Return 1 for same transactions
    function int compare(PcieTransaction tr,integer withdata=1);
      int same = 1; // Suppose that are same

        if (transType != tr.transType) same = 0;
        if (supported != tr.supported) same = 0;
        if (barHitN != tr.barHitN) same = 0;        
        if (tc != tr.tc) same = 0;
        if (td != tr.td) same = 0;
        if (ep != tr.ep) same = 0;
        if (attr != tr.attr) same = 0;
        if (length != tr.length) same = 0;
        if (busnum_req != tr.busnum_req) same = 0;
        if (devnum_req != tr.devnum_req) same = 0;
        if (funcnum_req != tr.funcnum_req) same = 0;

      if ((transType == CPLD))
        if (tag != tr.tag) same = 0;
      
      if (transType == CPLD) begin
        if (busnum_cpl != tr.busnum_cpl) same = 0;
        if (devnum_cpl != tr.devnum_cpl) same = 0;
        if (funcnum_cpl != tr.funcnum_cpl) same = 0;
        if (cplStatus != tr.cplStatus) same = 0;
        if (bcm != tr.bcm) same = 0;
        if (byteCount != tr.byteCount) same = 0;
        if (lowerAddr != tr.lowerAddr) same = 0;
      end
      else begin
        if (firstBE != tr.firstBE) same = 0;
        if (lastBE != tr.lastBE) same = 0;
        if (address != tr.address) same = 0;
      end

      if (withdata == 1) begin
        for (integer i=0; i < data.size; i++)
          if (data[i] != tr.data[i]) same=0;
      end
      compare = same;
    endfunction : compare

    //-- Show transaction -----------------------------------------------------
    // Function show transaction in text format
    function void display(integer full=0);

      if (supported)
        $write("Transaction: TYPE=");   
      else
        $write("Unsupported: TYPE=");    
        
      case (transType)
        RD32:
          $write("RD32,");
        RD64:
          $write("RD64,");
        WR32:
          $write("WR32,");
        WR64:
          $write("WR64,");
        CPLD:
          $write("CPLD,");
      endcase;

      $write("LENGTH=%0x,",length);

      case (transType)
        RD32,RD64,WR32,WR64: begin
          $write("lastBE=%0x,",lastBE);
          $write("firstBE=%0x,",firstBE);
          $write("ADDR=%0x,",address);
          $write("BARHIT_N=%s,",barHitN);
          end
        CPLD: begin
          $write("BYTECOUNT=%0x,",byteCount);
          $write("LOWERADDR=%0x,",lowerAddr);
          $write("CPLSTAT=%0x,",cplStatus);
          end
      endcase;

      $write("TAG=%0x,",tag);
      $write("TC=%0x,",tc);
      $write("TD=%0x,",td);
      $write("EP=%0x,",ep);
      $write("ATTR=%0x,",attr);
      $write("BUSNUM_REQ=%0x,",busnum_req);
      $write("DEVNUM_REQ=%0x,",devnum_req);
      $write("FUNCNUM_REQ=%0x,",funcnum_req);

      if (transType == CPLD) begin
        $write("BUSNUM_CPL=%0x,",busnum_cpl);
        $write("DEVNUM_CPL=%0x,",devnum_cpl);
        $write("FUNCNUM_CPL=%0x,",funcnum_cpl);
        $write("BCM=%0x\n",bcm);
      end
      else
        $write("\n");

      // Write also data for specified transaction types
      if (full && (transType == CPLD || transType == WR32 || transType == WR64) )
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
    endfunction

    // -- Private Class Methods --

    //-- Randomize data ------------------------------------------------------- 
    // This function is called after randomize function
    function void post_randomize();
      // treat length 0 as 1024 
      int length_10_0 = (length == 0) ? 1024 : length;
                                                                                 
      // clear unuseful bits
      address[1:0] = 2'b00;
      
      case (transType)
         RD32, WR32 :
            address[63:32] = 32'h00000000;
      endcase;
               
      if ( !enTxDelay )
        txDelay = 0;

      // correct values of byte enables
      if (length == 1) begin
        lastBE  = L0000;      
        firstBE = post_randomize_FirstBE();
      end

      // no sense to generate CPLD transactions
      if (transType == CPLD) begin
        $write("Error: It has no sense to generate CPLD transaction without being answer to some G2LRead!");
        $stop;
      end
        
      // Randomize data
      case (transType)
        WR32, WR64: 
        begin
          data = new[length_10_0*4 - minusBE()];                          
          for (integer i=0; i < data.size; i++)
            data[i] = $urandom_range(0,255);
        end                                                 
      endcase;
                                                               
     endfunction : post_randomize

    // -- Post Randomize First Byte Enables -----------------------------------
    // Re-randomize value for FirstBE (in case of length 1)
    function eFirstEnable post_randomize_FirstBE();
      int randNum = $urandom_range(0,9);

      case (randNum)
        0: post_randomize_FirstBE = F1111;
        1: post_randomize_FirstBE = F1110;
        2: post_randomize_FirstBE = F1100;
        3: post_randomize_FirstBE = F1000;           
        4: post_randomize_FirstBE = F0111; 
        5: post_randomize_FirstBE = F0011; 
        6: post_randomize_FirstBE = F0110; 
        7: post_randomize_FirstBE = F0100; 
        8: post_randomize_FirstBE = F0010; 
        9: post_randomize_FirstBE = F0001; 
      endcase             
    endfunction : post_randomize_FirstBE    

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
      copy.busnum_req = busnum_req; 
      copy.devnum_req = devnum_req; 
      copy.funcnum_req = funcnum_req;
      copy.busnum_cpl = busnum_cpl; 
      copy.devnum_cpl = devnum_cpl; 
      copy.funcnum_cpl = funcnum_cpl;
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

      copy.txDelay         = txDelay;
      copy.enTxDelay       = enTxDelay;
      copy.enInsideTxDelay = enInsideTxDelay;
    
      copy.RD32_wt = RD32_wt; 
      copy.RD64_wt = RD64_wt; 
      copy.WR32_wt = WR32_wt; 
      copy.WR64_wt = WR64_wt; 
      copy.CPLD_wt = CPLD_wt; 

      copy.txDelayEn_wt             = txDelayEn_wt; 
      copy.txDelayDisable_wt        = txDelayDisable_wt;
      copy.insideTxDelayEn_wt       = insideTxDelayEn_wt; 
      copy.insideTxDelayDisable_wt  = insideTxDelayDisable_wt;

      copy.F1111_wt = F1111_wt; 
      copy.F1110_wt = F1110_wt; 
      copy.F1100_wt = F1100_wt; 
      copy.F1000_wt = F1000_wt;
      copy.L1111_wt = L1111_wt; 
      copy.L0111_wt = L0111_wt; 
      copy.L0011_wt = L0011_wt; 
      copy.L0001_wt = L0001_wt;
      copy.L0000_wt = L0000_wt;

      copy.txDelayLow          = txDelayLow;
      copy.txDelayHigh         = txDelayHigh;
      copy.insideTxDelay       = insideTxDelay; 
    
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

    // -- Get length in B ------------------------------------------------------------
    // Count data length in bytes
    function integer getLengthInB();
      int length_10_0 = (length == 0) ? 1024 : length;

      if (transType == CPLD)
        getLengthInB = data.size;
      else
        getLengthInB = length_10_0*4 - minusBE();             
    endfunction : getLengthInB 

  endclass : PcieTransaction


  // -- Trnsaction mailbox ----------------------------------------------------
  typedef mailbox #(PcieTransaction) tPcieTransMbx;

endpackage : pcie_transaction_pkg
