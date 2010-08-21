//
// pcie_scoreboard_pkg.sv: PCIE part of Scoreboard
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
// $Id: pcie_scoreboard_pkg.sv 688 2007-10-19 16:11:56Z tomalek $
//

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package pcie_scoreboard_pkg;

  import ib_transaction_pkg::*;        // Internal Bus Transaction package
  import ib_driver_pkg::*;             // Internal Bus Driver package
  import ib_monitor_pkg::*;            // Internal Bus Monitor package
  import ib_table_pkg::*;              // Internal Bus transaction table package

  import pcie_transaction_pkg::*;      // PCIE Transaction package
  import pcie_driver_pkg::*;           // PCIE Driver package
  import pcie_monitor_pkg::*;          // PCIE Monitor package  
  import pcie_table_pkg::*;            // PCIE transaction table package  
  
  // --------------------------------------------------------------------------
  // -- PCIe Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardPcieDriverCbs extends PcieDriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    IbTransactionTable       ibTransTable;
    PcieTransactionTable     pcieTransTable;
    tPcieTransMbx            pcieTransMbx;    
    virtual iPcieCfg.bridge  pcieCFG;
    integer                  localTag;     // actual tag for local IB operations
    bit                      slaveEnable;
    bit                      turn;

    const bit SLAVE_TURN   = 1'b1;
    const bit ANSWER_TURN  = 1'b0;        
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (IbTransactionTable ibTransTable, 
                  PcieTransactionTable pcieTransTable,
                  tPcieTransMbx pcieTransMbx,
                  virtual iPcieCfg.bridge  pcieCFG);
      this.ibTransTable   = ibTransTable;
      this.pcieTransTable = pcieTransTable;
      this.pcieTransMbx   = pcieTransMbx;
      this.pcieCFG = pcieCFG;
      localTag = 0;
      slaveEnable = 0;
      turn = ANSWER_TURN;      
    endfunction

    // ------------------------------------------------------------------------
    // Function is called before is transaction sended (scoreboard)
    // transaction)
    virtual task pre_tx(ref PcieTransaction transaction, integer driverId);     

      // If slave transactions are not enabled or it's 'answer to G2LRead' turn, then answer 
      if ((slaveEnable == 0) || (turn == ANSWER_TURN)) 
        answerToGlobalRead(transaction); 
      else
        turn = ANSWER_TURN;

      // Process PCIE transaction and generate appropriate IB/PCIE transactions into IB/PCIE tables        
      if (transaction.supported) begin
        case (transaction.transType)
          WR32:          
            processWR(transaction);
          WR64:
            processWR(transaction);
          RD32: begin
            processRD(transaction);
           end
          RD64: begin
            processRD(transaction);
           end
          CPLD: begin 
            processCPLD(transaction);
            end
        endcase;
      end
    endtask

    // -- Answer To Global Read -----------------------------------------------
    // Take global read from mailbox and generate appropriate CPLDs
    task answerToGlobalRead (ref PcieTransaction transaction);
      int available = 1;
      PcieTransaction cpldTr; 

      if (slaveEnable == 1)
        available = pcieTransMbx.try_get(cpldTr);
      else
        pcieTransMbx.get(cpldTr);

      if (available == 1) begin
        turn   = SLAVE_TURN;
        transaction = cpldTr;
      end
    endtask           

    // -- Process WR transaction ----------------------------------------------
    // Store expected L2LW transaction into IB table
    task processWR (PcieTransaction transaction);

      InternalBusTransaction ibTr = new();        

      ibTr.localAddr    = countLocalAddr({transaction.address[31:2],countAddr10(transaction.firstBE)},transaction.barHitN);   
      ibTr.globalAddr   = {60'h000000000F00000,2'b00,countAddr10(transaction.firstBE)};  
      ibTr.tag          = localTag;        
      ibTr.length       = (transaction.data.size == 4096) ? 0 : transaction.data.size;
      ibTr.transType    = L2LW;  
      ibTr.data         = new[transaction.data.size];                          
      
      for (integer i=0; i < transaction.data.size; i++) ibTr.data[i] = transaction.data[i]; 
      
      ibTransTable.add(ibTr);
    endtask

    // -- Process CPLD transaction --------------------------------------------
    // Store expected RDCL transaction into IB table (only data is important)
    task processCPLD (PcieTransaction transaction);

      InternalBusTransaction ibTr = new();     

      ibTr.transType = (transaction.data.size == transaction.byteCount) ? RDCL : RDC; 
      ibTr.data      = new[transaction.data.size];                          
      
      for (integer i=0; i < transaction.data.size; i++) ibTr.data[i] = transaction.data[i]; 

      ibTransTable.add(ibTr); 
    endtask        

    // -- Process RD transaction ----------------------------------------------
    // Store expected L2LR transaction into IB table
    task processRD (PcieTransaction transaction);       
      generateIbTr(transaction);
      generatePcieTr(transaction);  
    endtask    

    // -- Generate PCIE transaction -------------------------------------------
    // Store expected CPLDs transactions into PCIE table
    task generatePcieTr (PcieTransaction transaction);
      bit          first     = 1;
      logic [6:0]  lowerAddr =  {transaction.address[6:2],countAddr10(transaction.firstBE)};
      integer      byteCount = (transaction.length == 0) ? 4096 - minusBE(transaction.firstBE,transaction.lastBE)
                                                         : transaction.length*4 - minusBE(transaction.firstBE,transaction.lastBE);
      integer      MAX_SIZE  = decodeMaxPcieSize(pcieCFG.MAX_PAYLOAD_SIZE);
      integer      lengthB;
      integer      lenaux;

      if ((byteCount >= MAX_SIZE) || (byteCount + lowerAddr[1:0] > 256))
        lengthB = MAX_SIZE - lowerAddr[6:0];
      else
        lengthB = byteCount;

      // parse into individual transaction ----------------
      do begin
        PcieTransaction pcieTr = new();       
         
        if (first)
           first = 0;
        else begin
           lowerAddr  = 0;
           byteCount -= lengthB;
           lengthB    = (byteCount > MAX_SIZE) ? MAX_SIZE - lowerAddr[6:0]
                                               : byteCount;
        end                  
        
        lenaux = (lengthB + lowerAddr[1:0] + 3) / 4;
        
        pcieTr.lowerAddr    = lowerAddr;      
        pcieTr.transType    = CPLD; 
        pcieTr.length       = (lenaux    == 1024) ? 0 : lenaux;
        pcieTr.byteCount    = (byteCount == 4096) ? 0 : byteCount;
        pcieTr.tag          = transaction.tag;              
        pcieTr.tc           = transaction.tc;      
        pcieTr.td           = 0;         
        pcieTr.ep           = 0;
        pcieTr.attr         = transaction.attr;  
        pcieTr.barHitN      = B1111110;
        pcieTr.supported    = 1;
        pcieTr.busnum_cpl   = pcieCFG.BUS_NUM;
        pcieTr.devnum_cpl   = pcieCFG.DEVICE_NUM;
        pcieTr.funcnum_cpl  = pcieCFG.FUNC_NUM;     
        pcieTr.busnum_req   = transaction.busnum_req; 
        pcieTr.devnum_req   = transaction.devnum_req; 
        pcieTr.funcnum_req  = transaction.funcnum_req;
        pcieTr.cplStatus    = CPLSTAT_OK;
        pcieTr.bcm          = 0;
        
        pcieTransTable.add(pcieTr);
      end while (byteCount != lengthB);        
       
    endtask       
    
    // -- Generate IB transaction ---------------------------------------------
    // Store expected L2LR transaction into IB table
    task generateIbTr (PcieTransaction transaction);

      InternalBusTransaction ibTr = new();
      int length_aux              = (transaction.length == 1024) ? 0 : transaction.length; 

      ibTr.localAddr    = countLocalAddr({transaction.address[31:2],countAddr10(transaction.firstBE)},transaction.barHitN);  
      ibTr.globalAddr   = {60'h000000000F00000,2'b00,countAddr10(transaction.firstBE)};  
      ibTr.length       = transaction.length*4 - transaction.minusBE();
      ibTr.transType    = L2LR;  
      ibTr.tag          = localTag;

      localTag = inc(localTag);
      
      ibTransTable.add(ibTr);
    endtask       

    // -- Count Local Addr ----------------------------------------------------
    // Count local address from mask, address and bar_base
    function logic [31:0] countLocalAddr(logic [31:0] address, logic [6:0] barHit);
      logic [31:0] barBase; 
      logic [31:0] barMask;       
      
      if      (barHit[0] == 0) barBase = 32'h01000000; 
      else if (barHit[1] == 0) barBase = 32'h02000000; 
      else if (barHit[2] == 0) barBase = 32'h03000000; 
      else if (barHit[3] == 0) barBase = 32'h04000000; 
      else if (barHit[4] == 0) barBase = 32'h06000000; 
      else if (barHit[5] == 0) barBase = 32'h08000000; 
      else if (barHit[6] == 0) barBase = 32'h0A000000; 

      if      (barHit[0] == 0) barMask = 32'h00FFFFFF;
      else if (barHit[1] == 0) barMask = 32'h00FFFFFF;
      else if (barHit[2] == 0) barMask = 32'h00FFFFFF;
      else if (barHit[3] == 0) barMask = 32'h01FFFFFF;
      else if (barHit[4] == 0) barMask = 32'h01FFFFFF;
      else if (barHit[5] == 0) barMask = 32'h01FFFFFF;
      else if (barHit[6] == 0) barMask = 32'h01FFFFFF;      
         
      countLocalAddr = (barMask & address) | (~barMask & barBase);
    endfunction : countLocalAddr   
    
    // -- Count Addr [1:0] ----------------------------------------------------
    // Count address [1:0] from first byte enables
    function logic [1:0] countAddr10(logic [3:0] firstBE);
      case (firstBE)
        4'b1111: countAddr10 = 2'b00;
        4'b1110: countAddr10 = 2'b01;
        4'b1100: countAddr10 = 2'b10;
        4'b1000: countAddr10 = 2'b11;
        4'b0111: countAddr10 = 2'b00; 
        4'b0011: countAddr10 = 2'b00; 
        4'b0110: countAddr10 = 2'b01; 
        4'b0100: countAddr10 = 2'b10; 
        4'b0010: countAddr10 = 2'b01; 
        4'b0001: countAddr10 = 2'b00;         
      endcase;
    endfunction : countAddr10        

    // -- Increment ------------------------------------------------------
    // Increment function as for 32-item cyclic buffer pointer
    function integer inc(integer tag);
       if (++tag == 32) tag = 0;
       inc = tag;
    endfunction : inc   

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

    // -- minus BE ------------------------------------------------------------
    // Count how is length in byte shortened
    function integer minusBE(eFirstEnable firstBE, eLastEnable lastBE);
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
      endcase;

      case (lastBE)
        L1111: last  = 0;
        L0111: last  = 1;
        L0011: last  = 2;
        L0001: last  = 3;
        L0000: last  = 0;
      endcase;

      minusBE = last + first;     
    endfunction : minusBE    
        
  endclass : ScoreboardPcieDriverCbs

  // --------------------------------------------------------------------------
  // -- Pcie Monitor Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardPcieMonitorCbs extends PcieMonitorCbs;
    // ---------------------
    // -- Class Variables --
    // ---------------------
    PcieTransactionTable    pcieTransTable;
    tPcieTransMbx           pcieTransMbx;    
    virtual iPcieCfg.bridge pcieCFG;
    logic [7:0]             globalMemory[*];   
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (PcieTransactionTable pcieTransTable, 
                  tPcieTransMbx pcieTransMbx,
                  virtual iPcieCfg.bridge  pcieCFG);
      this.pcieTransTable = pcieTransTable;
      this.pcieTransMbx   = pcieTransMbx;
      this.pcieCFG        = pcieCFG;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    virtual task post_rx(PcieTransaction transaction, integer monitorId);                
      // Receive transaction
      case (transaction.transType)
        RD32: begin 
          readFromGlobalMemory(transaction);
          pcieTransTable.removeNoData(transaction);
          end
        RD64: begin 
          readFromGlobalMemory(transaction); 
          pcieTransTable.removeNoData(transaction);
          end
        WR32: begin
          writeToGlobalMemory(transaction);
          pcieTransTable.remove(transaction);  
          if (transaction.tag[7] == 1) begin      
            transaction.transType=CPLD;
            pcieTransTable.removeCpldData(transaction); // it checks data and transType          
          end
          end
        WR64: begin
          writeToGlobalMemory(transaction); 
          pcieTransTable.remove(transaction);
          if (transaction.tag[7]== 1) begin     
            transaction.transType=CPLD;
            pcieTransTable.removeCpldData(transaction); // it checks data and transType          
          end
          end
        CPLD: begin                                                                             
          pcieTransTable.removeNoData(transaction);
          pcieTransTable.removeCpldData(transaction); // it checks data and transType
          end
      endcase;
    endtask

    // -- Read from global memory ---------------------------------------------
    // Generate CPLD transactions as answer to master read 
    task readFromGlobalMemory(PcieTransaction transaction);

      // read from global memory and create CPLD transaction
      PcieTransaction cpldTr = transaction.copy();
      longint unsigned  from = {transaction.address[63:2],countAddr10(transaction.firstBE)};

      cpldTr.lowerAddr    = {transaction.address[6:2],countAddr10(transaction.firstBE)};      
      cpldTr.transType    = CPLD; 
      cpldTr.length       = transaction.length;
      cpldTr.byteCount    = transaction.getLengthInB();
      cpldTr.barHitN      = B1111110;
      cpldTr.supported    = 1;
      cpldTr.busnum_cpl   = 0; 
      cpldTr.devnum_cpl   = 0;
      cpldTr.funcnum_cpl  = 0;
      cpldTr.cplStatus    = CPLSTAT_OK;
      cpldTr.bcm          = 0;   
      cpldTr.txDelay         = $urandom_range(0,5);
      cpldTr.enTxDelay       = 1;
      cpldTr.enInsideTxDelay = 1;      
      cpldTr.data         = new[cpldTr.byteCount];                          
      
      for (integer i=0; i < cpldTr.data.size; i++) begin
        if (!globalMemory.exists(from + i)) globalMemory[from + i] = $urandom_range(0,255);
        cpldTr.data[i] = globalMemory[from + i];
      end

      // parse CPLD transaction into more smaller CPLDs according to PCIE completion rules
      parseCPLD(cpldTr);
      
    endtask           

    // -- Parse CPLD transaction ----------------------------------------------
    // Parse CPLD transaction to more smaller ones according to PCIE cpl rules
    task parseCPLD (PcieTransaction transaction);
      bit          first     = 1;
      logic [6:0]  lowerAddr = transaction.lowerAddr;
      integer      byteCount = (transaction.byteCount == 0) ? 4096 : transaction.byteCount;
      integer      MAX_SIZE  = decodeMaxPcieSize(pcieCFG.MAX_PAYLOAD_SIZE);
      integer      lengthB;
      integer      dataLo;
      integer      dataHi;
      integer      ind;
      integer      lenaux;

      if ((byteCount >= MAX_SIZE) || (byteCount + lowerAddr[1:0] > 256))
        lengthB = MAX_SIZE - lowerAddr[6:0];
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
           lowerAddr  = 0;
           byteCount -= lengthB;
           lengthB    = (byteCount > MAX_SIZE) ? MAX_SIZE : byteCount;
           dataHi    += lengthB;
        end        

        lenaux = (lengthB + lowerAddr[1:0] + 3) / 4;
        
        pcieTr.lowerAddr    = lowerAddr;      
        pcieTr.transType    = CPLD; 
        pcieTr.length       = (lenaux    == 1024) ? 0 : lenaux;
        pcieTr.byteCount    = (byteCount == 4096) ? 0 : byteCount;
        pcieTr.tag          = transaction.tag;              
        pcieTr.tc           = transaction.tc;      
        pcieTr.td           = 0;         
        pcieTr.ep           = 0;
        pcieTr.attr         = transaction.attr;  
        pcieTr.barHitN      = B1111110;
        pcieTr.supported    = 1;
        pcieTr.busnum_cpl   = transaction.busnum_cpl; 
        pcieTr.devnum_cpl   = transaction.devnum_cpl; 
        pcieTr.funcnum_cpl  = transaction.funcnum_cpl;
        pcieTr.busnum_req   = transaction.busnum_req; 
        pcieTr.devnum_req   = transaction.devnum_req; 
        pcieTr.funcnum_req  = transaction.funcnum_req;
        pcieTr.cplStatus    = CPLSTAT_OK;
        pcieTr.bcm          = 0;
        pcieTr.txDelay         = $urandom_range(0,5);;
        pcieTr.enTxDelay       = 1;
        pcieTr.enInsideTxDelay = 1;              
        pcieTr.data         = new[lengthB];                       
        
        ind = 0; 
        for (int i=dataLo; i < dataHi; i++) pcieTr.data[ind++] = transaction.data[i];         
                        
        pcieTransMbx.put(pcieTr);    
      end while (byteCount != lengthB);        
      
    endtask    

    // -- Write to global memory ----------------------------------------------
    // Write data from WR32/64 transaction to global memory 
    task writeToGlobalMemory(PcieTransaction transaction);
      longint unsigned from = {transaction.address[63:2],countAddr10(transaction.firstBE)};
      longint unsigned   to = from + transaction.data.size;
       
      for (longint unsigned i=from; i < to; i++) globalMemory[i] = transaction.data[i-from];   
    endtask               

    // -- Count Addr [1:0] ----------------------------------------------------
    // Count address [1:0] from first byte enables
    function logic [1:0] countAddr10(logic [3:0] firstBE);
      case (firstBE)
        4'b1111: countAddr10 = 2'b00;
        4'b1110: countAddr10 = 2'b01;
        4'b1100: countAddr10 = 2'b10;
        4'b1000: countAddr10 = 2'b11;
        4'b0111: countAddr10 = 2'b00; 
        4'b0011: countAddr10 = 2'b00; 
        4'b0110: countAddr10 = 2'b01; 
        4'b0100: countAddr10 = 2'b10; 
        4'b0010: countAddr10 = 2'b01; 
        4'b0001: countAddr10 = 2'b00;         
      endcase;
    endfunction : countAddr10    

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
    
  endclass : ScoreboardPcieMonitorCbs  
  
endpackage : pcie_scoreboard_pkg



