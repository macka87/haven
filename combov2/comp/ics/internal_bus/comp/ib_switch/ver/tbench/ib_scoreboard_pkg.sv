/*
 * ib_scoreboard_pkg.sv: Internal Bus Scoreboard
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobiersky <kobiersky@liberouter.org>
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
 * $Id: ib_scoreboard_pkg.sv 334 2007-09-05 20:13:22Z xkobie00 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package ib_scoreboard_pkg;

  import ib_transaction_pkg::*; // Transaction package
  import ib_driver_pkg::*;      // Driver calls back class
  import ib_monitor_pkg::*;     // Monitor pkg
  import test_pkg::*;           // Test pkg

  // -- Score board structure -------------------------------------------------
  typedef struct {
    InternalBusTransaction transaction;
    integer from;
    integer to;
    } tScoreboardItem;

  // --------------------------------------------------------------------------
  // -- Scoreboard table
  // --------------------------------------------------------------------------
  class ScoreboardTable;
     // ---------------------
     // -- Class Variables --
     // ---------------------
     tScoreboardItem scoreboard[$]; // Scoreboard
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
    // Add item to scoreboard
    task add(tScoreboardItem item);
       lock();
       this.scoreboard.push_back(item); // Insert item to scoreboard
       added++;
       unlock();
    endtask: add
    
    // ------------------------------------------------------------------------
    // Add item to scoreboard
    task remove(integer i);
       this.scoreboard.delete(i); // Insert item to scoreboard
       removed--;
    endtask: remove
    
    // ------------------------------------------------------------------------
    // Lock scoreboard
    task lock();
       sem.get(1);
    endtask: lock

    // ------------------------------------------------------------------------
    // Unlock scoreboard
    task unlock();
       sem.put(1);
    endtask: unlock
    
    // ------------------------------------------------------------------------
    // Belongs to Switch address space
    task display(integer full=0);
       lock();
       $write("----------------------------------------------------------------\n");
       $write("-- SCOREBOARD\n");
       $write("----------------------------------------------------------------\n");
       $write("Size: %d\n", scoreboard.size);
       $write("Items added: %d\n", added);
       $write("Items removed: %d\n", removed);
       foreach(scoreboard[i]) scoreboard[i].transaction.display(full);
       $write("----------------------------------------------------------------\n");
       unlock();
    endtask: display

  endclass : ScoreboardTable


  // --------------------------------------------------------------------------
  // -- Internal Bus Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardDriverCbs extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    ScoreboardTable scoreboard;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (ScoreboardTable scoreboard);
      this.scoreboard = scoreboard;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction sended (scoreboard)
    // transaction)
    virtual task post_tx(InternalBusTransaction transaction, integer driverId);
       // Insert transaction to scoreboard
       //$write("Driver %d sends packet:\n", driverId); transaction.display(1);
         
       insertToScoreboard(transaction, driverId);
    endtask

    // ------------------------------------------------------------------------
    // Insert transaction to scoreboard (if it is not  suposed to be droped by switch)
    task insertToScoreboard(InternalBusTransaction transaction, integer driverId);
      integer drop;
      integer targetPort;
      tScoreboardItem item;
       if (driverId > 0) // Transaction from downstream port
         // Belongs to downstream port0, but not to from which is comming
         if ( belongsDownstream(transaction, 0) && (driverId !=1) ) begin
           drop = 0; 
           targetPort = 1;
           end 
         else if (belongsDownstream(transaction, 1) && (driverId != 2)) begin
           drop = 0; 
           targetPort = 2;
           end
         else if (!belongsSwitch(transaction)) begin
           drop = 0;
           targetPort = 0;
           end
         else
           drop = 1;
       
       else begin
          // Transaction from upstream port
          if ( belongsDownstream(transaction, 0) ) begin
            drop= 0;
            targetPort = 1;
            end
          else if ( belongsDownstream(transaction, 1) ) begin
            drop= 0;
            targetPort = 2;
            end
          else
             drop = 1;
        end;

       if (!drop) begin
         item.transaction = transaction;
         item.from = driverId;
         item.to   = targetPort;
         this.scoreboard.add(item); // Insert item to scoreboard
         //$write("Adding from driver %d to port %d\n", driverId, targetPort); transaction.display(1);
         end;
    endtask: insertToScoreboard

    // ------------------------------------------------------------------------
    // Belongs to Downstream address space
    function integer belongsDownstream(InternalBusTransaction transaction, integer downstreamId);
       case (transaction.transType)
         L2LW, L2LR:
            if (downstreamId == 0)
               belongsDownstream = (transaction.localAddr <= (cDownstream0Base+cDownstream0Limit)) &&
                                   (transaction.localAddr >= cDownstream0Base);
            else
               belongsDownstream = (transaction.localAddr <= (cDownstream1Base+cDownstream1Limit)) &&
                                   (transaction.localAddr >= cDownstream1Base);
         L2GW, G2LR:
               belongsDownstream = 0;
                                  
         RDC, RDCL:
            if (downstreamId == 0)
               belongsDownstream = (transaction.globalAddr[31:0] <= (cDownstream0Base+cDownstream0Limit)) &&
                                   (transaction.globalAddr[31:0] >= cDownstream0Base);
            else
               belongsDownstream = (transaction.globalAddr[31:0] <= (cDownstream1Base+cDownstream1Limit)) &&
                                   (transaction.globalAddr[31:0] >= cDownstream1Base);
       endcase;
    endfunction: belongsDownstream

    // ------------------------------------------------------------------------
    // Belongs to Switch address space
    function integer belongsSwitch(InternalBusTransaction transaction);
       case (transaction.transType)
         L2LW, L2LR:
               belongsSwitch = (transaction.localAddr <= (cSwitchBase+cSwitchLimit)) &&
                                   (transaction.localAddr >= cSwitchBase);
         L2GW, G2LR:
               belongsSwitch = 0;
                                  
         RDC, RDCL:
               belongsSwitch = (transaction.globalAddr[31:0] <= (cSwitchBase+cSwitchLimit)) &&
                               (transaction.globalAddr[31:0] >= cSwitchBase);
       endcase;
    endfunction: belongsSwitch
 
  endclass : ScoreboardDriverCbs


  // --------------------------------------------------------------------------
  // -- Internal Bus Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardMonitorCbs extends MonitorCbs;
    
    // ---------------------
    // -- Class Variables --
    // ---------------------
    ScoreboardTable scoreboard;
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (ScoreboardTable scoreboard);
      this.scoreboard = scoreboard;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    virtual task post_rx(InternalBusTransaction transaction, integer monitorId);
      integer auxRemove=0;
      //$write("Received transaction from monitor: %d \n", monitorId);transaction.display(1);
      scoreboard.lock();
      for (integer i=0; i < scoreboard.scoreboard.size; i++)
      begin
        if ( (scoreboard.scoreboard[i].to == monitorId) &&
             (scoreboard.scoreboard[i].transaction.compare(transaction) == 1 )) begin
              auxRemove = 1;
              scoreboard.remove(i);;
              end
       end
       scoreboard.unlock();
       if (auxRemove == 0) begin
         $write("Unknown transaction received from monitor %d\n", monitorId);
         transaction.display(1); 
         $stop;
         end;
    endtask

 
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
    ScoreboardTable      scoreTable;
    ScoreboardMonitorCbs monitorCbs;
    ScoreboardDriverCbs  driverCbs;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      this.scoreTable = new;
      this.monitorCbs = new(scoreTable);
      this.driverCbs  = new(scoreTable);
    endfunction
  
  endclass : Scoreboard




endpackage : ib_scoreboard_pkg

