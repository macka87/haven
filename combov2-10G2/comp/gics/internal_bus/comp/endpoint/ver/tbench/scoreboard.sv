/*
 * scoreboard.sv: Scoreboard for ib_endpoint verification
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
 * $Id: scoreboard.sv 14041 2010-06-15 13:15:55Z washek $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package scoreboard_pkg;

  import sv_common_pkg::*;      // Verification common package
  import ib_common_pkg::*;      // InternalBus common package
  import ib_params_pkg::*;
  import math_pkg::*;
  import ib_memory_transaction_pkg::*; // Memory transaction
  import done_transaction_pkg::*;      // Done transaction
  import ib_memory_pkg::*;             // Internal Bus memory
  import endpoint_coverage_pkg::*;     // Coverage class
  
  
  // --------------------------------------------------------------------------
  // -- Internal Bus Transaction Table
  // --------------------------------------------------------------------------
  class IbTransactionTable extends TransactionTable #(0,InternalBusTransaction);
    
    task remove(InternalBusTransaction transaction, bit compareData = 1);
      bit status;
      
      super.remove(transaction,status,compareData);
      
      if (status == 0) begin
        $write($time,"Error: Unable to remove Internal Bus transaction:\n");
        transaction.display();
      end
      
    endtask: remove
  
  endclass : IbTransactionTable
  
  // --------------------------------------------------------------------------
  // -- Memory Transaction Table
  // --------------------------------------------------------------------------
  class MemoryTransactionTable extends TransactionTable #(0,MemoryTransaction);
    
    task remove(MemoryTransaction transaction, bit compareData = 1);
      bit status;
      
      super.remove(transaction,status,compareData);
      
      if (status == 0) begin
        $write($time,"Error: Unable to remove Memory transaction:\n");
        transaction.display();
      end
      
    endtask: remove
  
  endclass : MemoryTransactionTable
  
  // --------------------------------------------------------------------------
  // -- BusMaster Done Transaction Table
  // --------------------------------------------------------------------------
  class DoneTransactionTable extends TransactionTable #(0,DoneTransaction);
    
    task remove(DoneTransaction transaction, bit compareData = 1);
      bit status;
      
      super.remove(transaction,status,compareData);
      
      if (status == 0) begin
        $write($time,"Error: Unable to remove Done transaction:\n");
        transaction.display();
        this.display();
      end
      
    endtask: remove
  
  endclass : DoneTransactionTable
  
  
  // --------------------------------------------------------------------------
  // -- Memory Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardMemoryCbs extends MemoryCbs;

    MemoryTransactionTable memTransTable;
    DoneTransactionTable   doneTransTable;

    // Constructor
    function new (MemoryTransactionTable memTransTable,
                  DoneTransactionTable   doneTransTable);
      this.memTransTable  = memTransTable;
      this.doneTransTable = doneTransTable;
    endfunction
    
    // Function is called after a write transaction is received
    virtual task writeTransReceived(MemoryTransaction tr, int memoryId);
      memTransTable.remove(tr);
    endtask
    
    // Function is called after a read request is received
    virtual task readReqReceived(MemoryTransaction tr, int memoryId);
      memTransTable.remove(tr);
    endtask
    
    // Function is called after a read data is sent
    virtual task readDataSent(MemoryTransaction tr, int memoryId);
      string diff;
      DoneTransaction doneTr;
      // Find corresponding doneTransaction (by addresses)
      // and set it as completed (done=1)
      for(int i=0; i < doneTransTable.tr_table.size; i++) begin 
        if (doneTransTable.tr_table[i].addr == tr.addr)
          doneTransTable.tr_table[i].done = 1;
      end
      
      memTransTable.add(tr);
    endtask
    
  endclass : ScoreboardMemoryCbs
  
  
  // --------------------------------------------------------------------------
  // -- Internal Bus Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardDriverCbs #(pIbEndpointGenerics G = dIbEndpointGenerics) 
                                                             extends DriverCbs;

    // -- Class Variables --
    IbTransactionTable     ibTransTable;
    MemoryTransactionTable memTransTable;
    DoneTransactionTable   doneTransTable;
    
    parameter int LOG2DWB = log2(G.DATA_WIDTH/8);
    
    // -- Constructor ---------------------------------------------------------
    function new (IbTransactionTable     ibTransTable,
                  MemoryTransactionTable memTransTable,
                  DoneTransactionTable   doneTransTable);
      this.ibTransTable   = ibTransTable;
      this.memTransTable  = memTransTable;
      this.doneTransTable = doneTransTable;
    endfunction

    // ------------------------------------------------------------------------
    // Function is called before a transaction is sent (scoreboard)
    virtual task pre_tx(ref Transaction transaction, string inst);
      InternalBusTransaction tr;
      $cast(tr, transaction);
      
      //check if it's in endpoint adress space
      if (G.CONNECTED_TO == SWITCH_SLAVE)
        if (tr.globalAddr <  G.ENDPOINT_BASE ||
            tr.globalAddr >= G.ENDPOINT_BASE + G.ENDPOINT_LIMIT)
          return;
      
      case (tr.transType)
        L2LW:               // Local to Local Read
          processL2LW(tr);
        L2LR:               // Local to Local Write
          processL2LR(tr);
        RDC:                // Read completition
          processRDC(tr);
        RDCL:               // Read completition (last packet)
          processRDC(tr);
      endcase;
    endtask

    // -- Process L2LW transaction --------------------------------------------
    // Parse L2LW transaction into Memory transactions
    task processL2LW (InternalBusTransaction transaction);
      MemoryTransaction memTr = new();

      memTr.transType = WRITE;
      memTr.addr      = transaction.globalAddr;
      memTr.length    = transaction.length;
      memTr.data      = transaction.data;

      memTransTable.add(memTr);
    endtask

    // -- Process L2LR transaction --------------------------------------------
    // Create Read Memory transaction and CPL IB transaction
    task processL2LR (InternalBusTransaction transaction);
      createReadRequest(transaction);
      createCompletion(transaction);
    endtask

    // -- Create Read Request -------------------------------------------------
    // Create Read Memory transaction
    task createReadRequest (InternalBusTransaction transaction);
      MemoryTransaction memTr = new();

      memTr.transType = READ_REQ;
      memTr.addr   = transaction.globalAddr;
      memTr.length = transaction.length;
      
      memTransTable.add(memTr);
    endtask

    // -- Create Completion ---------------------------------------------------
    // Create Completion Internal Bus Transaction
    task createCompletion (InternalBusTransaction transaction);
      InternalBusTransaction cpl;
      Transaction tr = transaction.copy();
      $cast(cpl, tr);
      cpl.transType  = RDCL;
      cpl.localAddr  = transaction.globalAddr;
      cpl.globalAddr = transaction.localAddr;
      
      ibTransTable.add(cpl);
    endtask
    
    // -- Process RDC transaction ---------------------------------------------
    // Parse RDC transaction into Memory transactions
    task processRDC (InternalBusTransaction transaction);
      MemoryTransaction memTr = new();

      memTr.transType = WRITE;
      memTr.addr      = transaction.globalAddr;
      memTr.length    = transaction.length;
      memTr.data      = transaction.data;

      memTransTable.add(memTr);
      
      // Create done transaction
      if (transaction.transType == RDCL) begin
        DoneTransaction doneTr = new;
        doneTr.tag  = transaction.tag;
        doneTransTable.add(doneTr);
      end
    endtask
    
  endclass : ScoreboardDriverCbs

  // --------------------------------------------------------------------------
  // -- Internal Bus Monitor Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardMonitorCbs #(int DATA_WIDTH = 64) extends MonitorCbs;

    // -- Class Variables --
    IbTransactionTable     ibTransTable;
    MemoryTransactionTable memTransTable;
    
    parameter int LOG2DWB = log2(DATA_WIDTH/8);
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (IbTransactionTable     ibTransTable,
                  MemoryTransactionTable memTransTable);
      this.ibTransTable = ibTransTable;
      this.memTransTable = memTransTable;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called after a transaction is received (scoreboard)
    virtual task post_rx(Transaction transaction, string inst);
      InternalBusTransaction tr;
      $cast(tr, transaction);
      
      case (tr.transType)
        L2LW: begin
          ibTransTable.remove(tr,0);
          removeMemoryTrans(tr);
          end
        L2LR: begin
          ibTransTable.remove(tr,0);
          end
        L2GW: begin
          ibTransTable.remove(tr,0);
          removeMemoryTrans(tr);
          end
        G2LR: begin
          ibTransTable.remove(tr,0);
          end
        RDC: begin
          // Error endpoint must send RDCL
          $write("Error: RDC transaction received from Endpoint\n");
          $stop;
          end
        RDCL: begin
          ibTransTable.remove(tr,0);
          removeMemoryTrans(tr);
          end
      endcase;
    endtask
   
    // ------------------------------------------------------------------------
    // Remove transaction from memory table
    task removeMemoryTrans(InternalBusTransaction transaction);
      MemoryTransaction memTrans = new;
      
      memTrans.transType = READ_DATA;
      memTrans.addr      = transaction.localAddr;
      memTrans.length    = transaction.length;
      memTrans.data      = transaction.data;
      
      memTransTable.remove(memTrans);
    endtask : removeMemoryTrans

  endclass : ScoreboardMonitorCbs


  // --------------------------------------------------------------------------
  // -- BusMaster Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardBmDriverCbs #(int DATA_WIDTH = 64) extends DriverCbs;
  
    // -- Class Variables --
    IbTransactionTable     ibTransTable;
    MemoryTransactionTable memTransTable;
    DoneTransactionTable   doneTransTable;
    
    parameter int LOG2DWB = log2(DATA_WIDTH/8);
    
    // -- Constructor ---------------------------------------------------------
    function new (IbTransactionTable     ibTransTable,
                  MemoryTransactionTable memTransTable,
                  DoneTransactionTable   doneTransTable);
      this.ibTransTable   = ibTransTable;
      this.memTransTable  = memTransTable;
      this.doneTransTable = doneTransTable;
    endfunction

    // ------------------------------------------------------------------------
    // Function is called before a transaction is sent
    virtual task pre_tx(ref Transaction transaction, string inst);
      InternalBusTransaction tr;
      MemoryTransaction memTr;
      DoneTransaction doneTr;
      $cast(tr, transaction);
      
      // Remove data (there should be only headers on BM ifc)
      tr.data.delete();
      
      // -- Read transaction --
      if (tr.transType == L2LR || tr.transType == G2LR)
        ibTransTable.add(tr); // Add header to IbTransTable
        
      // -- Write transaction --
      else if (tr.transType == L2LW || tr.transType == L2GW) begin
        // Add header to IbTransTable
        ibTransTable.add(tr);
        
        // Create memory read transaction
        memTr = new;
        memTr.transType = READ_REQ;
        memTr.addr   = tr.localAddr;
        memTr.length = tr.length;
        memTransTable.add(memTr);
        
        // Create done transaction
        doneTr = new;
        doneTr.tag  = tr.tag;
        doneTr.addr = memTr.addr;
        doneTr.done = 0;
        doneTransTable.add(doneTr);
      end
      
    endtask

  endclass : ScoreboardBmDriverCbs


  // --------------------------------------------------------------------------
  // -- BusMaster Monitor Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardBmMonitorCbs extends MonitorCbs;
    
    // -- Class Variables --
    DoneTransactionTable     doneTransTable;
    
    // -- Constructor ---------------------------------------------------------
    function new (DoneTransactionTable     doneTransTable);
      this.doneTransTable = doneTransTable;
    endfunction

    // ------------------------------------------------------------------------
    // Function is called after a transaction is received
    virtual task post_rx(Transaction transaction, string inst);
      DoneTransaction tr;
      $cast(tr, transaction);
      
      tr.done = 1;
      doneTransTable.remove(tr);
    endtask

  endclass : ScoreboardBmMonitorCbs

  
  

  // --------------------------------------------------------------------------
  // -- Scoreboard
  // --------------------------------------------------------------------------
  class Scoreboard #(pIbEndpointGenerics G = dIbEndpointGenerics);

    // -- Class Variables --
    IbTransactionTable      ibTransactionTable;
    MemoryTransactionTable  memoryTransactionTable;
    DoneTransactionTable    doneTransactionTable;

    ScoreboardMonitorCbs  #(G.DATA_WIDTH) monitorCbs;
    ScoreboardDriverCbs   #(G)            driverCbs;
    ScoreboardMemoryCbs                   memoryCbs;
    ScoreboardBmDriverCbs #(G.DATA_WIDTH) bmDriverCbs;
    ScoreboardBmMonitorCbs                bmMonitorCbs;

    // -- Constructor ---------------------------------------------------------
    function new ();
      this.ibTransactionTable       = new;
      this.memoryTransactionTable   = new;
      this.doneTransactionTable     = new;

      this.driverCbs    = new(ibTransactionTable, memoryTransactionTable, 
                              doneTransactionTable);
      this.monitorCbs   = new(ibTransactionTable, memoryTransactionTable);
      this.memoryCbs    = new(memoryTransactionTable, doneTransactionTable);
      this.bmDriverCbs  = new(ibTransactionTable, memoryTransactionTable,
                              doneTransactionTable);
      this.bmMonitorCbs = new(doneTransactionTable);
    endfunction
    
    // -- Tables are empty ----------------------------------------------------
    // Returns 1 if all transaction tables are empty, else returns 0.
    function bit tablesEmpty();
      if (ibTransactionTable.tr_table.size() == 0 &&
          memoryTransactionTable.tr_table.size() == 0 &&
          doneTransactionTable.tr_table.size() == 0 )
        tablesEmpty = 1;
      else
        tablesEmpty = 0;
    endfunction;
    
    // -- Reset ---------------------------------------------------------------
    // Clears all tables
    task reset();
      ibTransactionTable.tr_table = new[0];
      memoryTransactionTable.tr_table = new[0];
      doneTransactionTable.tr_table = new[0];
    endtask;
    
    // -- Display -------------------------------------------------------------
    task display();
      ibTransactionTable.display(1, "INTERNAL BUS");
      memoryTransactionTable.display(1, "MEMORY");
      if (G.BUS_MASTER_ENABLE)
        doneTransactionTable.display(1, "BUS MASTER DONE");
    endtask
    
  endclass : Scoreboard
  
endpackage : scoreboard_pkg

