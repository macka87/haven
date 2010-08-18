//
// ib_scoreboard_pkg.sv: IB part of Scoreboard
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
// $Id: ib_scoreboard_pkg.sv 688 2007-10-19 16:11:56Z tomalek $
//

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package ib_scoreboard_pkg;

  import ib_transaction_pkg::*;        // Internal Bus Transaction package
  import ib_driver_pkg::*;             // Internal Bus Driver package
  import ib_monitor_pkg::*;            // Internal Bus Monitor package
  import ib_table_pkg::*;              // Internal Bus transaction table package

  import pcie_transaction_pkg::*;      // PCIE Transaction package
  import pcie_driver_pkg::*;           // PCIE Driver package
  import pcie_monitor_pkg::*;          // PCIE Monitor package  
  import pcie_table_pkg::*;            // PCIE transaction table package  
   
  // --------------------------------------------------------------------------
  // -- IB Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardIbDriverCbs extends IbDriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    PcieTransactionTable     pcieTransTable;
    IbTransactionTable       ibTransTable;    
    tIbTransMbx              ibTransMbx;
    virtual iPcieCfg.bridge  pcieCFG;
    integer                  globalTag; // actual tag for global PCIE operations
    bit                      masterEnable;
    bit                      turn;

    const bit MASTER_TURN = 1'b1;
    const bit ANSWER_TURN  = 1'b0;    
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (PcieTransactionTable    pcieTransTable,
                  IbTransactionTable      ibTransTable,
                  tIbTransMbx             ibTransMbx,
                  virtual iPcieCfg.bridge pcieCFG   );
      this.pcieTransTable = pcieTransTable;
      this.ibTransTable = ibTransTable;
      this.ibTransMbx = ibTransMbx;
      this.pcieCFG = pcieCFG; 
      globalTag = 0;
      masterEnable = 0;
      turn = ANSWER_TURN;
    endfunction

    // ------------------------------------------------------------------------
    // Function is called before is transaction sended (scoreboard)
    // transaction)
    virtual task pre_tx(ref InternalBusTransaction transaction, integer driverId);                  

      // If master transactions are not enabled or it's 'answer to L2LRead' turn, then answer
      if ((masterEnable == 0) || (turn == ANSWER_TURN)) 
        answerToLocalRead(transaction); 
      else
        turn = ANSWER_TURN;                                                                    

      // Process IB transaction and generate appropriate IB/PCIE transactions into IB/PCIE tables
      case (transaction.transType)
        L2LW: begin
          //$write("Error: L2LW transaction must not come to BRIDGE!\n");
          //$stop;          
          end
        L2LR: begin
          //$write("Error: L2LR transaction must not come to BRIDGE!\n");
          //$stop;                     
          end
        L2GW: begin             
           processL2GW(transaction);
          end
        G2LR: begin 
           processG2LR(transaction);
          end
        RDC: begin
          //$write("Error: RDC transaction must not come to BRIDGE!\n");
          //$stop;                     
          end
        RDCL: begin 
          processRDCL(transaction);
          end
      endcase;                                                               
    endtask

    // -- Skip G2LR transaction -----------------------------------------------
    // Change actual G2LR transaction into L2GW in order to skip next G2LRs 
    task skipG2LR (ref InternalBusTransaction transaction);
       
      transaction.transType     = L2GW;
      transaction.globalAddr[2] = 0;
      transaction.data          = new[transaction.length];
      
      for (integer i=0; i < transaction.length; i++) 
         transaction.data[i] = $urandom_range(0,255);               
    endtask       
    
    // -- Answer To Local Read ------------------------------------------------
    // Take local IB read from mailbox and generate appropriate RDCL
    task answerToLocalRead (ref InternalBusTransaction transaction);
      int available = 1;
      InternalBusTransaction readTr; 

      if (masterEnable == 1)
        available = ibTransMbx.try_get(readTr);
      else
        ibTransMbx.get(readTr);

      if (available == 1) begin
        turn   = MASTER_TURN;
        
        transaction.localAddr    = readTr.localAddr;
        transaction.globalAddr   = {32'h00000000,readTr.globalAddr[31:0]};
        transaction.tag          = readTr.tag;
        transaction.length       = readTr.length;
        transaction.transType    = RDCL;
        transaction.data         = new[transaction.length];                          
        
        for (integer i=0; i < transaction.data.size; i++) 
          transaction.data[i] = readTr.data[i];        
      end
    endtask       

    // -- Process L2GW transaction --------------------------------------------
    // Store expected WR32/WR64 transaction into PCIe table
    task processL2GW (InternalBusTransaction transaction);
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
        pcieTr.tag          = globalTag;              
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
        
        ind = 0;
        for (integer i=dataLo; i < dataHi; i++) pcieTr.data[ind++] = transaction.data[i];         

        pcieTransTable.add(pcieTr);
      end while (byteCount != lengthB);        
      
    endtask

    // -- Process G2LR transaction --------------------------------------------
    // Store expected RD32/RD64 and RDC/RDCL into scoreboard tables
    task processG2LR (InternalBusTransaction transaction);
      generateReadPcieTr(transaction);
      generateCplIbTr(transaction);
    endtask    

    // -- Generate read PCIE transaction --------------------------------------
    // Store expected RD32/RD64 transaction into PCIe table
    task generateReadPcieTr (InternalBusTransaction transaction);

      PcieTransaction pcieTr = new();        
      int len                = (transaction.length == 0) ? 4096 : transaction.length;

      pcieTr.address      = {transaction.globalAddr[63:2],2'b00};      
      pcieTr.transType    = (pcieTr.address[63:32] == 32'h00000000) ? RD32 : RD64; 
      pcieTr.length       = (len + transaction.globalAddr[1:0] + 3) / 4;
      pcieTr.lastBE       = countLastBE(transaction.globalAddr[1:0],transaction.length[1:0],pcieTr.length);
      pcieTr.firstBE      = countFirstBE(transaction.globalAddr[1:0],transaction.length[1:0],pcieTr.length);
      pcieTr.tag          = globalTag;              
      pcieTr.tc           = 0;      
      pcieTr.td           = 0;         
      pcieTr.ep           = 0;
      pcieTr.attr         = 0;                
      pcieTr.supported    = 1;  
      pcieTr.barHitN      = B1111110;      
      pcieTr.busnum_req   = pcieCFG.BUS_NUM;
      pcieTr.devnum_req   = pcieCFG.DEVICE_NUM;
      pcieTr.funcnum_req  = pcieCFG.FUNC_NUM;

      globalTag = inc(globalTag);      
      
      pcieTransTable.add(pcieTr);
    endtask    

    // -- Generate RDC/RDCL IB transaction ------------------------------------
    // Store expected RDC/RDCL transactions into IB table
    task generateCplIbTr (InternalBusTransaction transaction);
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
        
        ibTr.transType    = (byteCount == lengthB) ? RDCL : RDC;
        ibTr.length       = (lengthB   == 4096) ? 0 : lengthB;
        ibTr.tag          = transaction.tag;              
        ibTr.globalAddr   = {32'h00000000,address};
        ibTr.localAddr    =  32'h0F000000; 
        
        ibTransTable.add(ibTr); 
      end while (byteCount != lengthB);        
       
    endtask           

    // -- Process RDCL transaction --------------------------------------------
    // Store expected CPLD / add data to L2GW transaction
    task processRDCL (InternalBusTransaction transaction);
      PcieTransaction pcieTr = new();     

      pcieTr.transType    = CPLD; 
      pcieTr.supported    = 1;
      pcieTr.data         = new[transaction.data.size];      
      
      for (integer i=0; i < transaction.data.size; i++) pcieTr.data[i] = transaction.data[i]; 
      
      pcieTransTable.add(pcieTr);         
    endtask    
    
    // -- Generate CPLD transaction -------------------------------------------
    // Store expected CPLD transaction into PCIe table (only data is important)
    task generateCPLD (InternalBusTransaction transaction);

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
            
  endclass : ScoreboardIbDriverCbs
  
  // --------------------------------------------------------------------------
  // -- Internal Bus Monitor Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardIbMonitorCbs extends IbMonitorCbs;
    // ---------------------
    // -- Class Variables --
    // ---------------------
    IbTransactionTable ibTransTable;
    tIbTransMbx        ibTransMbx;    
    logic [7:0]        localMemory[*];       
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (IbTransactionTable ibTransTable, tIbTransMbx ibTransMbx);
      this.ibTransTable = ibTransTable;
      this.ibTransMbx   = ibTransMbx;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    virtual task post_rx(InternalBusTransaction transaction, integer monitorId);
      // Receive transaction
      case (transaction.transType)
        L2GW: begin
          $write("Error: L2GW transaction received from PCIe bridge\n");
          $stop;
          end
        G2LR: begin
          $write("Error: G2LR transaction received from PCIe bridge\n");
          $stop;
          end
        L2LW: begin                                                          
          writeToLocalMemory(transaction);        
          ibTransTable.remove(transaction);
          if (transaction.tag[7] == 1) begin      
            transaction.transType = (transaction.tag[8] == 1) ? RDCL : RDC;
            ibTransTable.removeCplData(transaction); // it checks data and transType          
          end 
          
          end
        L2LR: begin
          readFromLocalMemory(transaction);
          ibTransTable.removeNoData(transaction);
          end
        RDC: begin
          ibTransTable.removeCplData(transaction); // it checks data and transType           
          ibTransTable.removeNoData(transaction);            
          end
        RDCL: begin 
          ibTransTable.removeCplData(transaction); // it checks data and transType        
          ibTransTable.removeNoData(transaction);
          end
      endcase;
    endtask

    // -- Read from local memory ----------------------------------------------
    // Read data from local memory
    task readFromLocalMemory(InternalBusTransaction transaction);

      InternalBusTransaction tr = transaction.copy;         
      longint unsigned     from = transaction.localAddr;
      int                auxlen = (tr.length == 0) ? 4096 : tr.length;

      tr.data = new[auxlen];                          
      
      for (integer i=0; i < auxlen; i++) begin
        if (!localMemory.exists(from + i)) localMemory[from + i] = $urandom_range(0,255);
        tr.data[i] = localMemory[from + i];
      end

      ibTransMbx.put(tr);                                        
      if (ibTransMbx.num() > 32) $write("Error: Too many (%d) local read in-process!\n",ibTransMbx.num());             
    endtask               

    // -- Write to local memory -----------------------------------------------
    // Write data from L2LW transaction to local memory 
    task writeToLocalMemory(InternalBusTransaction transaction);
      longint unsigned from = transaction.localAddr;
      longint unsigned   to = from + transaction.data.size;
       
      for (longint unsigned i=from; i < to; i++) localMemory[i] = transaction.data[i-from];   
    endtask                   
    
  endclass : ScoreboardIbMonitorCbs

endpackage : ib_scoreboard_pkg



