/*
 * scoreboard_pkg.sv: Scoreboard
 * Copyright (C) 2007 CESNET
 * Author(s): Tomas Malek <tomalek@liberouter.org>
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
 * $Id: scoreboard_pkg.sv 333 2007-09-05 20:07:59Z xkobie00 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package scoreboard_pkg;

  import ib_transaction_pkg::*;        // Transaction package
  // import bm_transaction_pkg::*;     // Bus Master Transaction package
  // import bm_driver_pkg::*;          // Bus Master Driver package
  import ib_memory_transaction_pkg::*; // Memory transaction
  import ib_memory_pkg::*;             // Internal Bus memory
  import ib_driver_pkg::*;             // Internal Bus Driver package
  import ib_monitor_pkg::*;            // Internal Bus Monitor package

  // --------------------------------------------------------------------------
  // -- IB Transaction table
  // --------------------------------------------------------------------------
  class IbTransactionTable;
     // ---------------------
     // -- Class Variables --
     // ---------------------
     InternalBusTransaction tab[$]; // table
     semaphore sem;
     integer added;
     integer removed;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      sem = new(1);
      added = 0;
      removed = 0;
    endfunction
    
    // ------------------------------------------------------------------------
    // Add item to table
    task add(InternalBusTransaction item);
       lock();
       this.tab.push_back(item); // Insert item to table
       added++;
       unlock();
    endtask: add
    
    // ------------------------------------------------------------------------
    // Add item to table
    task remove(InternalBusTransaction transaction);
      bit auxRemove = 0;
      lock();
      for (integer i=0; i < tab.size; i++) begin
        if (tab[i].compare(transaction) == 1) begin
          auxRemove = 1;
          tab.delete(i);
          removed--;
          break;
          end
      end
      unlock();
      
      if (!auxRemove) begin 
        $write("Error: Unable to remove Internal Bus transaction:  ");
        transaction.display();
        end
    endtask: remove

    // ------------------------------------------------------------------------
    // Add item to table
    task removeNoData(InternalBusTransaction transaction);
      bit auxRemove = 0;
      lock();
      for (integer i=0; i < tab.size; i++) begin
        if (tab[i].compare(transaction,0) == 1) begin
          auxRemove = 1;
          tab.delete(i);
          removed--;
          break;
          end
      end
      unlock();
      
      if (!auxRemove) begin 
        $write("Error: Unable to remove Internal Bus transaction:  ");
        transaction.display();
        end
    endtask: removeNoData
    
    
    // ------------------------------------------------------------------------
    // Lock table
    task lock();
       sem.get(1);
    endtask: lock

    // ------------------------------------------------------------------------
    // Unlock table
    task unlock();
       sem.put(1);
    endtask: unlock
    
    // ------------------------------------------------------------------------
    // Belongs to Switch address space
    task display(integer full=0);
       lock();
       $write("----------------------------------------------------------------\n");
       $write("-- IbTransaction Table\n");
       $write("----------------------------------------------------------------\n");
       $write("Size: %d\n", tab.size);
       $write("Items added: %d\n", added);
       $write("Items removed: %d\n", removed);
       foreach(tab[i]) tab[i].display(0);
       $write("----------------------------------------------------------------\n");
       unlock();
    endtask: display
  endclass : IbTransactionTable

  // --------------------------------------------------------------------------
  // -- Memory Transaction table
 // --------------------------------------------------------------------------
  class MemoryTransactionTable;
     // ---------------------
     // -- Class Variables --
     // ---------------------
     MemoryTransaction tab[$]; // table
     semaphore sem;
     integer added;
     integer removed;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      sem = new(1);
      added = 0;
      removed = 0;
    endfunction
    
    // ------------------------------------------------------------------------
    // Add item to table
    task add(MemoryTransaction item);
       lock();
       this.tab.push_back(item); // Insert item to table
       added++;
       unlock();
    endtask: add
    
    // ------------------------------------------------------------------------
    // Add item to table
    task remove(MemoryTransaction transaction);
      bit auxRemove = 0;
      lock();
      for (integer i=0; i < tab.size; i++) begin
        if (tab[i].compare(transaction) == 1) begin
          auxRemove = 1;
          tab.delete(i);
          removed--;
          break;
          end
      end
      unlock();
      if (!auxRemove) begin 
        $write("Error: Unable to remove memory transaction:  ");
        transaction.display();
   //     if (transaction.transType == READ_DATA) begin
//           display();
//           $stop;
//           end;
        end
  
    endtask: remove
    
    // ------------------------------------------------------------------------
    // Lock table
    task lock();
       sem.get(1);
    endtask: lock

    // ------------------------------------------------------------------------
    // Unlock table
    task unlock();
       sem.put(1);
    endtask: unlock
    
    // ------------------------------------------------------------------------
    // Belongs to Switch address space
    task display(integer full=0);
       lock();
       $write("----------------------------------------------------------------\n");
       $write("-- MemoryTransaction Table\n");
       $write("----------------------------------------------------------------\n");
       $write("Size: %d\n", tab.size);
       $write("Items added: %d\n", added);
       $write("Items removed: %d\n", removed);
       foreach(tab[i]) tab[i].display();
       $write("----------------------------------------------------------------\n");
       unlock();
    endtask: display
  endclass : MemoryTransactionTable

  // --------------------------------------------------------------------------
  // -- Scoreboard Memory table
  // --------------------------------------------------------------------------
  class ScoreboardMemory;
     // ---------------------
     // -- Class Variables --
     // ---------------------
     logic [7:0] assoc_mem[*];  // Associative memory
     semaphore sem;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      sem = new(1);
    endfunction
    
    // ------------------------------------------------------------------------
    // Add item to tabl
    task write(MemoryTransaction item);
//       item.display();
       lock();
       for (int i = 0; i< 8; i++)
         if (item.be[i])
           for (int j = 0; j < 8; j++)
             assoc_mem[item.addr+i][j] = item.data[i*8+j];
       unlock();
    endtask: write
    
    // ------------------------------------------------------------------------
    // Add item to table
    task read(MemoryTransaction req, ref MemoryTransaction result);
      bit curr_bit;
      result.addr      = req.addr;
      result.be        = req.be;
      result.transType = READ_DATA;
      lock();
      for (integer i = 0; i < 64; i++) begin // Resolve byte enables
        if (assoc_mem.exists(req.addr+i/8) && req.be[i/8])
          curr_bit = assoc_mem[req.addr+i/8][i%8];
        else
          curr_bit = 1'b0; // Return zeros when reading from empty location
        result.data[i] = curr_bit;
        end // for
      unlock();
    endtask: read
    
    // ------------------------------------------------------------------------
    // Lock table
    task lock();
       sem.get(1);
    endtask: lock

    // ------------------------------------------------------------------------
    // Unlock table
    task unlock();
       sem.put(1);
    endtask: unlock
    
    // ------------------------------------------------------------------------
    // Belongs to Switch address space
    task display(integer full=0);
       lock();
       $write("----------------------------------------------------------------\n");
       $write("-- Scoreboard Memory\n");
       $write("----------------------------------------------------------------\n");
       // TODO: Print writen fields
       $write("----------------------------------------------------------------\n");
       unlock();
    endtask: display
  endclass : ScoreboardMemory
  
  // --------------------------------------------------------------------------
  // -- Internal Bus Memory Callbacks
  // --------------------------------------------------------------------------
  /* This is a abstract class for creating objects which get benefits from
   * function callback. This object can be used with InternalBusMemory
   * class. Inheritence from this basic class is neaded for functionality.
   */
  class ScoreboardMemoryCbs extends MemoryCbs;

    ScoreboardMemory scoreboardMemory;
    MemoryTransactionTable memTransTable;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (ScoreboardMemory scoreboardMemory, MemoryTransactionTable memTransTable);
      this.scoreboardMemory = scoreboardMemory;
      this.memTransTable    = memTransTable;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called after any memory request, completition
    virtual task memory_transaction(MemoryTransaction transaction, integer memoryId);
      case (transaction.transType)
        READ_REQ:
          // Read data from memory and insert it into transMemory table
          readReqTransaction(transaction, memoryId);
        READ_DATA:
          // Do nothing
          ;
        WRITE:
           // Remove from transaction memory
           writeTransaction(transaction, memoryId);
      endcase;
    endtask

    // ------------------------------------------------------------------------
    // Read data from memory and insert it into transMemory table
    task readReqTransaction(MemoryTransaction transaction, integer memoryId);
       MemoryTransaction newReadTrans;
 
       // Remove read request
       memTransTable.remove(transaction);
         
       // Insert readed data into memory table
       newReadTrans = new;
       scoreboardMemory.read(transaction, newReadTrans);
       memTransTable.add(newReadTrans);
    endtask : readReqTransaction
    
    // ------------------------------------------------------------------------
    // Remove write transaction from MemoryTransactionTable
    task writeTransaction(MemoryTransaction transaction, integer memoryId);
       memTransTable.remove(transaction);
       scoreboardMemory.write(transaction);
    endtask : writeTransaction
    
  endclass : ScoreboardMemoryCbs
  
  // --------------------------------------------------------------------------
  // -- Internal Bus Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardDriverCbs extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    IbTransactionTable ibTransTable;
    MemoryTransactionTable memTransTable;
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (IbTransactionTable ibTransTable, MemoryTransactionTable memTransTable);
      this.ibTransTable = ibTransTable;
      this.memTransTable = memTransTable;
    endfunction

    // ------------------------------------------------------------------------
    // Function is called before is transaction sended (scoreboard)
    // transaction)
    virtual task pre_tx(ref InternalBusTransaction transaction, integer driverId);
      case (transaction.transType)
        L2LW:          
          processL2LW(transaction);
        L2LR:
          processL2LR(transaction);
        RDC:          
          processRDC(transaction);
        RDCL:
          processRDC(transaction);
      endcase;
    endtask

        // -- Process L2LW transaction --------------------------------------------
    // Parse L2LW transaction into Memory transactions
    task processL2LW (InternalBusTransaction transaction);
  
      logic [31:0] addr = 32'h00000000;         // Memory Transaction address
      logic [7 :0] be   = 8'h00;                // Memory Transaction BE
      logic [63:0] data = 64'h0000000000000000; // Memory Transaction data

      int word64    = (transaction.length + transaction.localAddr[2:0] + 7)/8;
      int data_low  = 0;
      int data_high = 7;
      int trdata_i  = 0;

      // create individual transactions and store them into memTran. table
      for (int i=1; i <= word64; i++) begin
        
        MemoryTransaction memTr = new();        

        // first memory transaction
        if (i == 1) begin 
          data_low = transaction.localAddr[2:0];  
          be       = countFirstBE(transaction.localAddr[2:0]);
          addr     = {transaction.localAddr[31:3],3'b000};  
        end 
        // middle memory transactions
        else begin
          addr      = addr + 8;
          data_low  = 0;
          be        = 8'hFF;          
        end
        // last memory transaction
        if (i == word64) begin        
          be         = be & countLastBE(transaction.localAddr[2:0], transaction.length);   
          data_high  = ( ((transaction.length + transaction.localAddr[2:0]) - 1) % 8);   
        end
               
        // memory transaction data copying
        data = 64'h0000000000000000;
        for (int memdata_i = data_low; memdata_i <= data_high ; memdata_i++) begin           
          for (int j=memdata_i*8; j<memdata_i*8+8; j++)
            data[j] = transaction.data[trdata_i][j%8]; 
          trdata_i++;         
        end          
  
        // memory transaction storing
        memTr.addr      = addr;
        memTr.be        = be;     
        memTr.data      = data;
        memTr.transType = WRITE;
        memTransTable.add(memTr);        
      end

    endtask

    // -- Process L2LR transaction --------------------------------------------
    // Create Read Memory transaction and CPL IB transaction
    task processL2LR (InternalBusTransaction transaction);
      createReadRequest(transaction);
      createCompletion(transaction);
    endtask

      // -- Process RDC transaction ----------------------------------------------
    // Parse RDC transaction into Memory transactions
    task processRDC (InternalBusTransaction transaction);
  
      logic [31:0] addr = 32'h00000000;         // Memory Transaction address
      logic [7 :0] be   = 8'h00;                // Memory Transaction BE
      logic [63:0] data = 64'h0000000000000000; // Memory Transaction data

      int word64    = (transaction.length + transaction.globalAddr[2:0] + 7)/8;
      int data_low  = 0;
      int data_high = 7;
      int trdata_i  = 0;

      // create individual transactions and store them into memTran. table
      for (int i=1; i <= word64; i++) begin
        
        MemoryTransaction memTr = new();        

        // first memory transaction
        if (i == 1) begin 
          data_low = transaction.globalAddr[2:0];  
          be       = countFirstBE(transaction.globalAddr[2:0]);
          addr     = {transaction.globalAddr[31:3],3'b000};  
        end 
        // middle memory transactions
        else begin
          addr      = addr + 8;
          data_low  = 0;
          be        = 8'hFF;          
        end
        // last memory transaction
        if (i == word64) begin        
          be         = be & countLastBE(transaction.globalAddr[2:0], transaction.length);   
          data_high  = ( ((transaction.length + transaction.globalAddr[2:0]) - 1) % 8);   
        end
               
        // memory transaction data copying
        data = 64'h0000000000000000;
        for (int memdata_i = data_low; memdata_i <= data_high ; memdata_i++) begin           
          for (int j=memdata_i*8; j<memdata_i*8+8; j++)
            data[j] = transaction.data[trdata_i][j%8]; 
          trdata_i++;         
        end          
  
        // memory transaction storing
        memTr.addr      = addr;
        memTr.be        = be;     
        memTr.data      = data;
        memTr.transType = WRITE;
        memTransTable.add(memTr);        
      end

    endtask

    // -- Create Read Request -------------------------------------------------
    // Create Read Memory transaction
    task createReadRequest (InternalBusTransaction transaction);

      logic [31:0] addr = 32'h00000000;         // Memory Transaction address
      logic [7 :0] be   =  8'h00;               // Memory Transaction BE
      logic [63:0] data = 64'h0000000000000000; // Memory Transaction data

      int word64    = (transaction.length + transaction.localAddr[2:0] + 7)/8;

      // create individual transactions and store them into memTran. table
      for (int i=1; i <= word64; i++) begin
        
        MemoryTransaction memTr = new();        

        // first memory transaction
        if (i == 1) begin 
          be       = countFirstBE(transaction.localAddr[2:0]);
          addr     = {transaction.localAddr[31:3],3'b000};  
        end 

        // middle memory transactions
        else begin
          addr      = addr + 8;
          be        = 8'hFF;          
        end
          
        // last memory transaction
        if (i == word64) begin        
          be         = be & countLastBE(transaction.localAddr[2:0], transaction.length);   
        end
                 
        // memory transaction storing
        memTr.addr      = addr;
        memTr.be        = be;     
        memTr.data      = data;
        memTr.transType = READ_REQ;
        memTransTable.add(memTr);        
      end
    endtask

    // -- Create Completion ---------------------------------------------------
    // Create Completion Internal Bus Transaction
    task createCompletion (InternalBusTransaction transaction);
      InternalBusTransaction cpl = transaction.copy();      
      cpl.transType = RDCL;    
      ibTransTable.add(cpl);
    endtask

    // -- Count First BE ------------------------------------------------------
    // Count first byte enables of memory transaction
    function logic [7:0] countFirstBE(logic [2:0] bits);
      case (bits)
        3'b000: countFirstBE = 8'b11111111;
        3'b001: countFirstBE = 8'b11111110;
        3'b010: countFirstBE = 8'b11111100;
        3'b011: countFirstBE = 8'b11111000;
        3'b100: countFirstBE = 8'b11110000;
        3'b101: countFirstBE = 8'b11100000;
        3'b110: countFirstBE = 8'b11000000;
        3'b111: countFirstBE = 8'b10000000;
      endcase;
    endfunction : countFirstBE

    // -- Count Last BE ------------------------------------------------------
    // Count last byte enables of memory transaction
    function logic [7:0] countLastBE(logic [2:0] bits, int length);
      int last = (bits + length) % 8;
      case (last)
        3'b000: countLastBE = 8'b11111111;
        3'b001: countLastBE = 8'b00000001;
        3'b010: countLastBE = 8'b00000011;
        3'b011: countLastBE = 8'b00000111;
        3'b100: countLastBE = 8'b00001111;
        3'b101: countLastBE = 8'b00011111;
        3'b110: countLastBE = 8'b00111111;
        3'b111: countLastBE = 8'b01111111;
      endcase;
    endfunction : countLastBE
    
  endclass : ScoreboardDriverCbs

  // --------------------------------------------------------------------------
  // -- Bus Master Monitor Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardMonitorCbs extends MonitorCbs;
    // ---------------------
    // -- Class Variables --
    // ---------------------
    IbTransactionTable ibTransTable;
    MemoryTransactionTable memTransTable;
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (IbTransactionTable ibTransTable, MemoryTransactionTable memTransTable);
      this.ibTransTable = ibTransTable;
      this.memTransTable = memTransTable;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    virtual task post_rx(InternalBusTransaction transaction, integer monitorId);
      // Receive transaction
      case (transaction.transType)
        L2LW: begin
          $write("Error: L2LW transaction received from Endpoint\n");
          $stop;
          end
        L2LR: begin
          $write("Error: L2LR transaction received from Endpoint\n");
          $stop;
          end
        L2GW: begin
          $write("Error: L2GW transaction received from Endpoint\n");
          $stop;
          end
        G2LR: begin
          $write("Error: G2LR transaction received from Endpoint\n");
          $stop;
          end
        RDC: begin
          // Error endpoint must send RDCL
          $write("Error: RDC transaction received from Endpoint\n");
          $stop;
          end
        RDCL:
          // Remove transaction from TransTable and remove read memory
          // transactions
          processRDCL(transaction, monitorId);
      endcase;
    endtask

    // ------------------------------------------------------------------------
    // Remove transaction from TransTable and remove read memory transactions
    task processRDCL(InternalBusTransaction transaction, integer monitorId);
      // Remove transaction from transaction table
      ibTransTable.removeNoData(transaction);
      // Insert read requests
      removeMemoryDataRead(transaction, monitorId);
    endtask

   
    // ------------------------------------------------------------------------
    // Remove all memory data read
    task removeMemoryDataRead(InternalBusTransaction transaction, integer monitorId);
      MemoryTransaction memTrans = new;
      int length                 = transaction.length;
      int align                  = transaction.localAddr[2:0];
      logic [31:0] localAddr     = {transaction.localAddr[31:3], 3'b000};
      int dataPos                = 0;
      int memTransCount;
      logic [63:0] data;
      logic [8:0]  be;
      int startIndex;

      if ( ((length+align)%8) >= 1)
         memTransCount =(length+align)/8+1;
      else
         memTransCount =(length+align)/8;
     
      for (int i=0; i < memTransCount; i++) begin
        data = 64'h0000000000000000;
        be   = 8'b00000000;
        if (i == 0)
           startIndex = align;
        else
           startIndex = 0;

        // Fill Data
        for (int j = startIndex; j < 8; j++) begin
          if (dataPos < length) begin
            for (int k = 0; k < 8; k++)
              data[j*8+k] = transaction.data[dataPos][k];
            dataPos++;
            be[j]=1;
          end;
        end;

        memTrans.addr      = localAddr;
        memTrans.be        = be;
        memTrans.data      = data;
        memTrans.transType = READ_DATA;
        localAddr = localAddr + 8;
        memTransTable.remove(memTrans);
      end;
    endtask : removeMemoryDataRead


  endclass : ScoreboardMonitorCbs


  // -- Constructor ---------------------------------------------------------
  // Create a class 
  // --------------------------------------------------------------------------
  // -- Scoreboard
  // --------------------------------------------------------------------------
  class Scoreboard;
    // ---------------------
    // -- Class Variables --
    // ---------------------
    IbTransactionTable        ibTransactionTable;
    MemoryTransactionTable    memoryTransactionTable;
    ScoreboardMemory          scoreboardMemory;

    //ScoreboardBmDriverCbs     bmDriverCbs;
    ScoreboardMonitorCbs      monitorCbs;
    ScoreboardDriverCbs       driverCbs;
    ScoreboardMemoryCbs       memoryCbs;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      this.ibTransactionTable       = new;
      this.memoryTransactionTable   = new;
      this.scoreboardMemory         = new;

      // this.bmDriverCbs  = new(ibTransactionTable);
      this.driverCbs    = new(ibTransactionTable, memoryTransactionTable);
      this.monitorCbs   = new(ibTransactionTable, memoryTransactionTable);
      this.memoryCbs    = new(scoreboardMemory, memoryTransactionTable);
    endfunction
  endclass : Scoreboard



endpackage : scoreboard_pkg

