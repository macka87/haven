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
  // -- IB Request
  // --------------------------------------------------------------------------
  class IbRequest;
    logic [31:0]         startAddress; // Adresses where completition data will be written
    int                  length;       // Length of request
    logic [31:0]         addrArray[$]; // Sended read requests for addresses
    logic [7:0]          tag;          // Tag
    bit                  lastCpl = 0;  // Last completition bit
    
    // -- Constructor ---------------------------------------------------------
    // Create a new request
    function new (logic [31:0] startAddress, logic [7:0] tag, int length, bit lastCpl);
      this.startAddress = startAddress;
      this.length = length;
      for (int i=0; i < length; i++)
        this.addrArray.push_back(startAddress+i);
      this.tag = tag;
      this.lastCpl = lastCpl;
    endfunction

    // ------------------------------------------------------------------------
    // Display request
    task display(integer full=0);
       $write("IB Read Request: startAddr:%x, tag:%x, length:%x\n", startAddress, tag, length);
    endtask

    // ------------------------------------------------------------------------
    // Compare functon (only tag)
    function bit compare(input IbRequest to);
      int same = 1; // Suppose that are same
      if (tag != to.tag) same = 0;
      compare = same;
    endfunction

    // ------------------------------------------------------------------------
    // Remove Address
    function bit removeAddr(logic [31:0] addr);
      int status = 0;
      for (int i=0; i < length; i++)
        if (addrArray[i] == addr) begin
          addrArray.delete(i);
          length = length - 1;
          status = 1;
          break;
          end;
      removeAddr = status;
    endfunction

    // ------------------------------------------------------------------------
    // Remove Address Requests
    function bit removeAddressRequests(logic [31:0] startAddress, int length);
      int status =1;
      for (int i=0; i<length; i++)
        if (!removeAddr(startAddress+i)) begin
          status=0;
          break;
          end;
      removeAddressRequests=status;
    endfunction

  endclass : IbRequest


  // --------------------------------------------------------------------------
  // -- PcieRequests Table
  // --------------------------------------------------------------------------
  class IbRequestsTable;
     // ---------------------
     // -- Class Variables --
     // ---------------------
     IbRequest req_table[$];    // Table of requests
     semaphore sem;             // Semaphore solve problems with 
                                // concurent acces to TransactionTable        
     integer added;             // Items added to TransactionTable
     integer removed;           // Items removed from TransactionTable
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      sem = new(1);
      added = 0;
      removed = 0;
    endfunction
    
    // ------------------------------------------------------------------------
    // Add item to the table
    task add(IbRequest req);
      lock();
      this.req_table.push_back(req);
      added++;
      unlock();
    endtask: add
    
    // ------------------------------------------------------------------------
    //Remove item from the table
    task remove(IbRequest req, ref bit status);
       string diff;
       status=0;
       lock();
       for(integer i=0; i < this.req_table.size; i++) begin  
         if (this.req_table[i].compare(req)==1) begin
           if (req_table[i].length > req.length) begin
             status = req_table[i].removeAddressRequests(req.startAddress, req.length);
             if (!status)
               $write("IB Request table: receiving completition with wrong address or size\n");
             if (req.lastCpl == 1)
               $write("IB Request table: Receiving non last completition with last bit\n");
             break;
             end
           else if (req_table[i].length == req.length) begin
             status = req_table[i].removeAddressRequests(req.startAddress, req.length);
             if (!status)
               $write("IB Request table: receiving completition with wrong address or size");
             if (req.lastCpl != 1)
               $write("IB Request table: Receiving completition with not last bit\n");
             if (status &&  req.lastCpl) begin
               req_table.delete(i);
               removed++;
               break;
               end
             end
           else if (req_table[i].length < req.length) begin
             $write("IB Request table: receiving completition with more data then expected");
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
       $write("-- IB Requests Table\n");
       $write("------------------------------------------------------------\n");
       $write("Size: %d\n", req_table.size);
       $write("Items added: %d\n", added);
       $write("Items removed: %d\n", removed);
       foreach(req_table[i]) req_table[i].display();
       $write("------------------------------------------------------------\n");
       unlock();
    endtask: display
endclass : IbRequestsTable



  // --------------------------------------------------------------------------
  // -- PciePostedCheckDriverCbs
  // --------------------------------------------------------------------------
  class IbPostedCheckDriverCbs extends DriverCbs;
    // ---------------------
    // -- Class Variables --
    // ---------------------
    IbRequestsTable req_table;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (IbRequestsTable req_table);
      this.req_table = req_table;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called before is transaction sended 
    // Allow modify transaction before is sended
    virtual task pre_tx(ref Transaction transaction, string inst);
//     $write("RECEVING IB REQUEST: \n");
//     transaction.display();
    endtask
  
    // ------------------------------------------------------------------------
    // Function is called after is transaction sended 
    virtual task post_tx(Transaction transaction, string inst);
      InternalBusTransaction ib;
      $cast(ib, transaction);
      if (ib.transType == G2LR)
         addByteReadRequests(ib);  // Get transaction type
    endtask

    // ------------------------------------------------------------------------
    // Add byte read requests into table 
    task addByteReadRequests(InternalBusTransaction ib);
      IbRequest request = new(ib.localAddr, ib.tag, ib.length, 1);
      //$write("ADDING REQUEST: \n");
      //request.display();
      req_table.add(request);
    endtask

   endclass : IbPostedCheckDriverCbs


  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  class IbPostedCheckMonitorCbs extends MonitorCbs;
    
    // ---------------------
    // -- Class Variables --
    // ---------------------
    IbRequestsTable req_table;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (IbRequestsTable req_table);
      this.req_table = req_table;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    virtual task post_rx(Transaction transaction, string inst);
      InternalBusTransaction ib;
      $cast(ib, transaction);
       // Get transaction type
      case (ib.transType)
         RDC, RDCL:
          removeByteReadRequests(ib);
      endcase;
    endtask

    // ------------------------------------------------------------------------
    // Add byte read requests into table 
    task removeByteReadRequests(InternalBusTransaction ib);
      IbRequest request;
      bit status=0;
      bit lastCpl = (ib.transType == RDCL) ? 1:0;
      request = new(ib.globalAddr[31:0], ib.tag, ib.length, lastCpl);

//      $write("RECEVING IB COMPLETITION: \n");
//      ib.display();
      //$write("REMOVING REQUEST: \n");
      //request.display();
      req_table.remove(request, status);
      
      if (status==0)begin
         $write("IB_POSTED_CHECKER: receives completition for non-existent read request or with wrong data\n");
         $timeformat(-9, 3, " ns", 8);
         $write("Time: %t\n", $time);
         ib.display(); 
         req_table.display();
         $stop;
      end;
    endtask


  endclass : IbPostedCheckMonitorCbs



  // -- Constructor ---------------------------------------------------------
  // Create a class 
  // --------------------------------------------------------------------------
  // -- Scoreboard
  // --------------------------------------------------------------------------
  class IbPostedCheck;
    // ---------------------
    // -- Class Variables --
    // ---------------------
    IbRequestsTable         scoreTable;
    IbPostedCheckMonitorCbs monitorCbs;
    IbPostedCheckDriverCbs  driverCbs;

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
  endclass : IbPostedCheck

