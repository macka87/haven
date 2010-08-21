/*
 * ib_rd_responder.sv: Internal Bus Read responder
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobierský <kobiersky@liberouter.org>
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
 *
 *
 * TODO:
 *
 */

 // --------------------------------------------------------------------------
  // -- Memory Transaction Class
  // --------------------------------------------------------------------------
  typedef struct {
    logic [31:0] addr;
    byte data;
  } sMemoryTransaction;

  // --------------------------------------------------------------------------
  // -- Scoreboard Memory table
  // --------------------------------------------------------------------------
  class InternalBusMemory;
     // ---------------------
     // -- Class Variables --
     // ---------------------
     byte assoc_mem[*];  // Associative memory
     semaphore sem;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      sem = new(1);
    endfunction
    
    // ------------------------------------------------------------------------
    // Add item to tabl
    task write(sMemoryTransaction item);
       lock();
       assoc_mem[item.addr] = item.data;
       unlock();
    endtask: write
    
    // ------------------------------------------------------------------------
    // Add item to table
    task read(logic [31:0] addr, ref sMemoryTransaction result);
      lock();
      result.addr      = addr;
      if (assoc_mem.exists(addr))
         result.data = assoc_mem[addr];
      else
         result.data = 8'h00; // Return zeros when reading from empty location
      result.data =  $urandom_range(0,255); // TODO : Random reading
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
    task display();
       lock();
       $write("----------------------------------------------------------------\n");
       $write("-- Internal Bus Memory\n");
       $write("----------------------------------------------------------------\n");
       // TODO:
       $write("----------------------------------------------------------------\n");
       unlock();
    endtask: display
  endclass : InternalBusMemory


  // --------------------------------------------------------------------------
  // -- Internal Bus Read Responder
  // --------------------------------------------------------------------------
  class InternalBusReadResponder extends MonitorCbs;

    bit enabled;
    string inst;
    protected int stream_id;
    protected int scenario_id;
    protected int data_id;
    InternalBusMemory memory;
    tTransMbx transMbx;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (string inst, int stream_id = -1, tTransMbx transMbx = null);
      if (transMbx == null)  
        this.transMbx = new();     // Create own mailbox
      else
        this.transMbx = transMbx;  // Use created mailbox

      enabled      = 0;         // Disable generator by default
      inst         = inst;
      memory       = new;       // Create Internal Bus memory
      transMbx     = new;       // New Transaction mailbox
      stream_id    = stream_id; // Set stream id
      scenario_id  = -1;        // Set default scenario
      data_id      = 0;         // Set default data identifier
    endfunction
 
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    virtual task post_rx(Transaction transaction, string inst);
      InternalBusTransaction ib;
      $cast(ib, transaction);
      if (enabled) begin
        case (ib.transType)
          L2LW:          
            processL2LW(ib);
          L2LR:
            processL2LR(ib);
          RDC, RDCL:          
            processRDC(ib);
        endcase;
      end;
    endtask

    //-------------------------------------------------------------------------
    /*
     * Enable generator for creating n Instances.
     */
    task setEnabled();
      enabled = 1;
    endtask : setEnabled
    
    //-------------------------------------------------------------------------
    /*
     * Disable generator immediately.
     */
    task setDisabled();
      this.enabled = 0;
    endtask : setDisabled
   
    // -- Process L2LW transaction --------------------------------------------
    // Parse L2LW transaction into Memory transactions
    task processL2LW (InternalBusTransaction transaction);
      sMemoryTransaction memTr; // Memory transaction
      int len = (transaction.length == 0) ? 4096 : transaction.length;
      for (int i=0; i<len; i++) begin
        memTr.addr = transaction.localAddr + i;
        memTr.data = transaction.data[i];
        memory.write(memTr);        
      end
    endtask

    // -- Process RDC transaction ----------------------------------------------
    // Parse RDC transaction into Memory transactions
    task processRDC (InternalBusTransaction transaction);
      sMemoryTransaction memTr; // Memory transaction
      int len = (transaction.length == 0) ? 4096 : transaction.length;
      for (int i=0; i<len; i++) begin
        memTr.addr = transaction.globalAddr[31:0] + i;
        memTr.data = transaction.data[i];
        memory.write(memTr);        
      end
    endtask

    // -- Process L2LR transaction --------------------------------------------
    // Create Read Memory transaction and CPL IB transaction
    task processL2LR(InternalBusTransaction transaction);
      sMemoryTransaction memTr;         // Memory transaction
      InternalBusTransaction cpl = new;
      int len = (transaction.length == 0) ? 4096 : transaction.length;
      assert(transaction.copy(cpl));
      cpl.stream_id    = stream_id;     // Set stream id
      cpl.scenario_id  = scenario_id;   // Set default scenario
      cpl.data_id      = data_id;       // Set instance count
      cpl.transType     = RDCL;
      cpl.data = new[len];
      for (int i=0; i<len; i++) begin
        memory.read(transaction.localAddr[31:0] + i, memTr);        
        cpl.data[i] = memTr.data;
      end
      transMbx.put(cpl);
    endtask
   
endclass : InternalBusReadResponder
