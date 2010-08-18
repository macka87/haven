//
// bm_scoreboard_pkg.sv: BM part of Scoreboard
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
// $Id: bm_scoreboard_pkg.sv 688 2007-10-19 16:11:56Z tomalek $
//

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package bm_scoreboard_pkg;

  import bm_transaction_pkg::*;        // BM Transaction package
  import bm_driver_pkg::*;             // BM Driver package
  import bm_monitor_pkg::*;            // BM Monitor package  
  import bm_table_pkg::*;              // BM transaction table package    
  
  import ib_transaction_pkg::*;        // Internal Bus Transaction package
  import ib_driver_pkg::*;             // Internal Bus Driver package
  import ib_monitor_pkg::*;            // Internal Bus Monitor package
  import ib_table_pkg::*;              // Internal Bus transaction table package

  import pcie_transaction_pkg::*;      // PCIE Transaction package
  import pcie_driver_pkg::*;           // PCIE Driver package
  import pcie_monitor_pkg::*;          // PCIE Monitor package  
  import pcie_table_pkg::*;            // PCIE transaction table package  
   
  // --------------------------------------------------------------------------
  // -- BM Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardBmDriverCbs extends BmDriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    PcieTransactionTable     pcieTransTable;
    IbTransactionTable       ibTransTable;    
    BmTransactionTable       bmTransTable;
    tBmTransMbx              bmTransMbx; 
    virtual iPcieCfg.bridge  pcieCFG;
    bit bmEnable;
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (PcieTransactionTable    pcieTransTable,
                  IbTransactionTable      ibTransTable,
                  BmTransactionTable      bmTransTable,
                  virtual iPcieCfg.bridge pcieCFG   );
      this.pcieTransTable = pcieTransTable;
      this.ibTransTable   = ibTransTable;
      this.bmTransTable   = bmTransTable;
      this.pcieCFG        = pcieCFG; 
      this.bmTransMbx     = new(1); 
      bmEnable            = 0;
    endfunction

    // ------------------------------------------------------------------------
    // Function is called before is transaction sended (scoreboard)
    // transaction)
    virtual task pre_tx(ref BusMasterTransaction transaction);

      // if bus master transactions are not enabled, then wait for enable
      if (bmEnable == 0) waitForEnable();

      // Process BM transaction and generate appropriate IB/PCIE transactions into IB/PCIE tables
      case (transaction.transType)
        BM_L2LW: begin
           bmTransTable.add(transaction);
          end
        BM_L2LR: begin
           bmTransTable.add(transaction);
          end
        BM_L2GW: begin             
           processL2GW(transaction);
          end
        BM_G2LR: begin
          processG2LR(transaction);
          end
      endcase;                                                               
    endtask

    // -- Wait For Enable -----------------------------------------------------
    // Wait for enabling of bus master transactions 
    task waitForEnable ();
      BusMasterTransaction tr = new();
      bmTransMbx.get(tr); 
    endtask    
    
    // -- Skip transaction ----------------------------------------------------
    // Change actual supported transaction to unsupported transaction to skip it 
    task skipTransaction (ref BusMasterTransaction transaction);
      transaction.transType = BM_L2LW;
    endtask    

    // -- Process G2LR transaction --------------------------------------------
    // Store expected RD32/RD64 and L2LW into scoreboard tables
    task processG2LR (BusMasterTransaction transaction);
      bmTransTable.add(transaction);
      generateRD(transaction);
      generateCplIbTr(transaction);
    endtask        

    // -- Generate RDC/RDCL IB transaction ------------------------------------
    // Store expected RDC/RDCL transactions into IB table
    task generateCplIbTr (BusMasterTransaction transaction);
      bit          first     = 1;
      logic [31:0] address   =  transaction.localAddr;
      logic [ 6:0] addr60    =  transaction.globalAddr[6:0];
      integer      byteCount = (transaction.length == 0) ? 4096 : transaction.length;
      integer      MAX_SIZE  = decodeMaxPcieSize(pcieCFG.MAX_PAYLOAD_SIZE);
      integer      lengthB;

      if ((byteCount >= MAX_SIZE) || (byteCount + addr60[1:0] > 256))
        lengthB = MAX_SIZE - addr60;
      else
        lengthB = byteCount;
                                                  
      // parse into individual transaction ----------------
      do begin
        InternalBusTransaction ibTr = new();       
         
        if (first)
           first = 0;
        else begin
           addr60     = 0;
           address   += lengthB;
           byteCount -= lengthB;
           lengthB    = (byteCount > MAX_SIZE) ? MAX_SIZE : byteCount;
        end                  
        
        ibTr.transType    = L2LW;
        ibTr.length       = (lengthB   == 4096) ? 0 : lengthB;
        ibTr.tag          = (byteCount == lengthB) ? 16'h0180 : 16'h0080; 
        ibTr.localAddr    = {32'h00000000,address};
        ibTr.globalAddr   =  32'h0F000000; 
        
        ibTransTable.add(ibTr); 
      end while (byteCount != lengthB);        
       
    endtask      
    
    // -- Generate read PCIE transaction --------------------------------------
    // Store expected RD32/RD64 transaction into PCIe table
    task generateRD(BusMasterTransaction transaction);

      PcieTransaction pcieTr = new();        
      int len                = (transaction.length == 0) ? 4096 : transaction.length;

      pcieTr.address      = {transaction.globalAddr[63:2],2'b00};      
      pcieTr.transType    = (pcieTr.address[63:32] == 32'h00000000) ? RD32 : RD64; 
      pcieTr.length       = (len + transaction.globalAddr[1:0] + 3) / 4;
      pcieTr.lastBE       = countLastBE(transaction.globalAddr[1:0],transaction.length[1:0],pcieTr.length);
      pcieTr.firstBE      = countFirstBE(transaction.globalAddr[1:0],transaction.length[1:0],pcieTr.length);
      pcieTr.tag          = 0;
      pcieTr.tc           = 0;      
      pcieTr.td           = 0;         
      pcieTr.ep           = 0;
      pcieTr.attr         = 0;                
      pcieTr.supported    = 1;  
      pcieTr.barHitN      = B1111110;      
      pcieTr.busnum_req   = pcieCFG.BUS_NUM;
      pcieTr.devnum_req   = pcieCFG.DEVICE_NUM;
      pcieTr.funcnum_req  = pcieCFG.FUNC_NUM;

      pcieTransTable.add(pcieTr);
    endtask
    
    // -- Process L2GW transaction --------------------------------------------
    // Store expected L2LR/WR32/WR64 transaction into IB/PCIE table
    task processL2GW (BusMasterTransaction transaction);       
      bmTransTable.add(transaction);      
      generateL2LR(transaction);
      generateL2GW(transaction); 
    endtask 

    // -- Generate L2GW transactions ------------------------------------------
    // Store expected WR32/WR64 transaction into PCIe table
    task generateL2GW (BusMasterTransaction transaction);
      bit          first     = 1;
      logic [63:0] address   =  transaction.globalAddr[63:0];
      integer      byteCount = (transaction.length == 0) ? 4096 : transaction.length;
      integer      MAX_SIZE  = decodeMaxPcieSize(pcieCFG.MAX_PAYLOAD_SIZE);
      integer      lengthB;
      integer      dataLo;
      integer      dataHi;
      integer      ind;

      if ((byteCount >= MAX_SIZE) || (byteCount + address[1:0] > 256))
        lengthB = MAX_SIZE - address[6:0];
      else
        lengthB = byteCount;

      dataLo = 0;
      dataHi = lengthB;                            

      // parse into individual transaction ----------------
      do begin
        PcieTransaction pcieTr = new();       
         
        if (first)
           first = 0;
        else begin
           dataLo    += lengthB;
           address   += lengthB;
           byteCount -= lengthB;
           lengthB    = (byteCount > MAX_SIZE) ? MAX_SIZE - address[6:0]
                                               : byteCount;
           dataHi    += lengthB;                                               
        end                  
        
        pcieTr.address      = {address[63:2],2'b00};      
        pcieTr.transType    = (pcieTr.address[63:32] == 32'h00000000) ? WR32 : WR64; 
        pcieTr.length       = (lengthB + address[1:0] + 3) / 4;
        pcieTr.lastBE       = countLastBE(address[1:0],lengthB[1:0],pcieTr.length);
        pcieTr.firstBE      = countFirstBE(address[1:0],lengthB[1:0],pcieTr.length);
        pcieTr.tag          = (byteCount != lengthB) ? 0 : 8'b10000000;              
        pcieTr.tc           = 0;      
        pcieTr.td           = 0;         
        pcieTr.ep           = 0;
        pcieTr.attr         = 0;  
        pcieTr.barHitN      = B1111110;
        pcieTr.supported    = 1;
        pcieTr.busnum_req   = pcieCFG.BUS_NUM;
        pcieTr.devnum_req   = pcieCFG.DEVICE_NUM;
        pcieTr.funcnum_req  = pcieCFG.FUNC_NUM;     
        pcieTr.data         = new[lengthB];                       
        
//        ind = 0;
//        for (integer i=dataLo; i < dataHi; i++) pcieTr.data[ind++] = $urandom_range(0,255);

        pcieTransTable.add(pcieTr);
      end while (byteCount != lengthB);        
      
    endtask     

    // -- Generate L2LR transaction -------------------------------------------
    // Store expected L2LR transaction into IB table
    task generateL2LR (BusMasterTransaction transaction);

      InternalBusTransaction ibTr = new();

      ibTr.localAddr    = transaction.localAddr;  
      ibTr.globalAddr   = {60'h000000000F000,transaction.tag[15:8],1'b0,transaction.globalAddr[2:0]};
      ibTr.length       = transaction.length;
      ibTr.transType    = L2LR;  
      ibTr.tag          = 0;
      
      ibTransTable.add(ibTr);
    endtask        

    // -- Count First BE ------------------------------------------------------
    // Count first byte enables
    function logic [3:0] countFirstBE(logic [1:0] addr, logic [1:0] len, int lenDW);
      if (lenDW == 1) begin
         logic [3:0] sel = {addr,len};         
         case (sel)
            4'b0000: countFirstBE = 4'b1111;
            4'b0001: countFirstBE = 4'b0001;
            4'b0010: countFirstBE = 4'b0011;
            4'b0011: countFirstBE = 4'b0111;

            4'b0101: countFirstBE = 4'b0010;
            4'b0110: countFirstBE = 4'b0110;
            4'b0111: countFirstBE = 4'b1110;            
                                 
            4'b1001: countFirstBE = 4'b0100;
            4'b1010: countFirstBE = 4'b1100;            
                                 
            4'b1101: countFirstBE = 4'b1000;
         endcase;         
      end
      else begin       
         case (addr)
           2'b00: countFirstBE = 4'b1111;
           2'b01: countFirstBE = 4'b1110;
           2'b10: countFirstBE = 4'b1100;
           2'b11: countFirstBE = 4'b1000;
         endcase;
      end
    endfunction : countFirstBE

    // -- Count Last BE -------------------------------------------------------
    // Count last byte enables
    function logic [3:0] countLastBE(logic [1:0] addr, logic [1:0] len, int lenDW);
      if (lenDW == 1)
         countLastBE = 4'b0000;
      else begin
        logic [1:0] result = addr + len;
        case (result)
          2'b00: countLastBE = 4'b1111;
          2'b01: countLastBE = 4'b0001;
          2'b10: countLastBE = 4'b0011;
          2'b11: countLastBE = 4'b0111;
        endcase;
      end
    endfunction : countLastBE     
    
    // -- Decode Max Pcie Size ------------------------------------------------
    // Decode maximal Pcie Payload size from 3-bit CFG vector
    function integer decodeMaxPcieSize(logic [2:0] maxSize);
      case (maxSize)
        3'b000:  decodeMaxPcieSize =  128;
        3'b001:  decodeMaxPcieSize =  256;
        3'b010:  decodeMaxPcieSize =  512;
        3'b011:  decodeMaxPcieSize = 1024;
        3'b100:  decodeMaxPcieSize = 2048;
        3'b101:  decodeMaxPcieSize = 4096;          
        default: decodeMaxPcieSize =  256;
      endcase;          
    endfunction: decodeMaxPcieSize     
              
  endclass : ScoreboardBmDriverCbs

  // --------------------------------------------------------------------------
  // -- Bus Master Monitor Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardBmMonitorCbs extends BmMonitorCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    BmTransactionTable bmTransTable;
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (BmTransactionTable bmTransTable);
      this.bmTransTable = bmTransTable;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    virtual task post_rx(BusMasterTransaction transaction);
      bmTransTable.remove(transaction);
    endtask
   
  endclass : ScoreboardBmMonitorCbs

endpackage : bm_scoreboard_pkg



