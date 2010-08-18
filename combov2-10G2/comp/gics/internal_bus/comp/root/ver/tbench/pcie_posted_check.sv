/*
 * pcie_posted_check.sv: PCIEe Posted transaction checker
 * Copyright (C) 2008 CESNET
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

import sv_common_pkg::*;
import sv_ib_pkg::*;
import sv_pcie_pkg::*;
  
  // --------------------------------------------------------------------------
  // -- PCIe Request
  // --------------------------------------------------------------------------
  class PcieRequest;
    logic [15:0]         requesterId;
    logic [7:0]          tag;
    int                  length;
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (logic [15:0] requesterId, logic [7:0] tag, int length);
      this.requesterId = requesterId;
      this.tag = tag;
      this.length = length;
    endfunction

    // ------------------------------------------------------------------------
    // Display request
    task display(integer full=0);
       $write("PCIe Read Request: requester_id:%x, tag:%x, length:%x\n", requesterId, tag, length);
    endtask: display

    // ------------------------------------------------------------------------
    // Compare functon
    function bit compare(input PcieRequest to);
      int same = 1; // Suppose that are same
      if (requesterId != to.requesterId) same = 0;
      if (tag != to.tag) same = 0;
      compare = same;
    endfunction : compare

  endclass : PcieRequest



  // --------------------------------------------------------------------------
  // -- PcieRequests Table
  // --------------------------------------------------------------------------
  class PcieRequestsTable;
     // ---------------------
     // -- Class Variables --
     // ---------------------
     PcieRequest req_table[$];    // Table of requests
     semaphore sem;               // Semaphore solve problems with 
                                  // concurent acces to TransactionTable        
     integer added;               // Items added to TransactionTable
     integer removed;             // Items removed from TransactionTable
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      sem = new(1);
      added = 0;
      removed = 0;
    endfunction
    
    // ------------------------------------------------------------------------
    // Add item to the table
    task add(PcieRequest req);
      lock();
      this.req_table.push_back(req);
      added++;
      unlock();
    endtask: add
    
    // ------------------------------------------------------------------------
    //Remove item from the table
    task remove(PcieRequest req, ref bit status);
       string diff;
       status=0;
       lock();
       for(integer i=0; i < this.req_table.size; i++) begin  
         if (this.req_table[i].compare(req)==1) begin
           if (req_table[i].length > req.length) begin
             req_table[i].length = req_table[i].length - req.length;
             status=1;
             break;
             end
           else if (req_table[i].length == req.length) begin
             req_table.delete(i);
             removed++;
             status=1;
             break;
             end
           else if (req_table[i].length < req.length) begin
             $write("PCIe Request table: receiving completition with more data then expected");
             status=0;
             break;
             end
           end
         end // for
       unlock();     
    endtask: remove 
    
    // ------------------------------------------------------------------------
    // Lock scoreboard 
    task lock();
       sem.get(1);                     // Semaphore is set to lock 
    endtask: lock

    // ------------------------------------------------------------------------
    // Unlock scoreboard
    task unlock();
       sem.put(1);                     // Semaphore is set to unlock
    endtask: unlock
    
    // ------------------------------------------------------------------------
    // Display the actual state of transaction table
    task display(integer full=0);
       lock();
       $write("------------------------------------------------------------\n");
       $write("-- PCIe Requests Table\n");
       $write("------------------------------------------------------------\n");
       $write("Size: %d\n", req_table.size);
       $write("Items added: %d\n", added);
       $write("Items removed: %d\n", removed);
       foreach(req_table[i]) req_table[i].display();
       $write("------------------------------------------------------------\n");
       unlock();
    endtask: display
endclass : PcieRequestsTable



  // --------------------------------------------------------------------------
  // -- PciePostedCheckDriverCbs
  // --------------------------------------------------------------------------
  class PciePostedCheckDriverCbs extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    PcieRequestsTable req_table;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (PcieRequestsTable req_table);
      this.req_table = req_table;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called before is transaction sended 
    // Allow modify transaction before is sended
    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction sended 
    virtual task post_tx(Transaction transaction, string inst);
      PcieTransaction pcie;
      $cast(pcie, transaction);
       // Get transaction type
      case (pcie.transType)
        RD32, RD64:
          addByteReadRequests(pcie);
      endcase;
    endtask

    // ------------------------------------------------------------------------
    // Add byte read requests into table 
    task addByteReadRequests(PcieTransaction pcie);
      PcieRequest request;
      int length = getLength(pcie);
      request = new(pcie.requesterId, pcie.tag, length);
      //$write("ADDING REQUEST: \n");
      //request.display();
      req_table.add(request);
    endtask

    // ------------------------------------------------------------------------
    // Function return length in bytes of read
    function int getLength(input PcieTransaction pcie);
      int length_10_0 = (pcie.length == 0) ? 1024 : pcie.length;
      getLength = length_10_0*4 - pcie.minusBE();
    endfunction;

   endclass : PciePostedCheckDriverCbs


  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  class PciePostedCheckMonitorCbs extends MonitorCbs;
    
    // ---------------------
    // -- Class Variables --
    // ---------------------
    PcieRequestsTable req_table;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (PcieRequestsTable req_table);
      this.req_table = req_table;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    virtual task post_rx(Transaction transaction, string inst);
      PcieTransaction pcie;
      $cast(pcie, transaction);
       // Get transaction type
      case (pcie.transType)
        CPLD_LAST, CPLD:
          removeByteReadRequests(pcie);
      endcase;
    endtask

    // ------------------------------------------------------------------------
    // Add byte read requests into table 
    task removeByteReadRequests(PcieTransaction pcie);
      PcieRequest request;
      int length = getLength(pcie);
      bit status=0;
      request = new(pcie.requesterId, pcie.tag, length);
      //$write("REMOVING REQUEST: \n");
      //request.display();
      req_table.remove(request, status);
      
      if (status==0)begin
         $write("PCIE_POSTED_CHECKER: receives completition for non-existent read request.\n");
         $timeformat(-9, 3, " ns", 8);
         $write("Time: %t\n", $time);
         pcie.display(); 
         req_table.display();
         $stop;
      end;
    endtask

    // ------------------------------------------------------------------------
    // Function return length in bytes of read, write or completition 
    function int getLength(input PcieTransaction pcie);
      int length_10_0;
      int cmpl_len;
      length_10_0 = (pcie.length == 0) ? 1024 : pcie.length;
      cmpl_len    = length_10_0*4 - pcie.lowerAddr[1:0];
      if (cmpl_len > pcie.byteCount)
        cmpl_len = pcie.byteCount;
      getLength = cmpl_len;
    endfunction;
  endclass : PciePostedCheckMonitorCbs



  // -- Constructor ---------------------------------------------------------
  // Create a class 
  // --------------------------------------------------------------------------
  // -- Scoreboard
  // --------------------------------------------------------------------------
  class PciePostedCheck;
    // ---------------------
    // -- Class Variables --
    // ---------------------
    PcieRequestsTable         scoreTable;
    PciePostedCheckMonitorCbs monitorCbs;
    PciePostedCheckDriverCbs  driverCbs;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      this.scoreTable = new;
      this.monitorCbs = new(scoreTable);
      this.driverCbs  = new(scoreTable);
    endfunction

    // -- Display -------------------------------------------------------------
    // Create a class 
    task display();
      scoreTable.display();
    endtask
  endclass : PciePostedCheck

