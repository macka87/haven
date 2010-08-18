/*
 * ib_scoreboard_pkg.sv: Internal Bus Transformer Scoreboard
 * Copyright (C) 2008 CESNET
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
 * $Id: ib_scoreboard_pkg.sv 1899 2008-03-26 15:52:13Z tomalek $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package ib_scoreboard_pkg;

  import ib_transaction_pkg::*; // Transaction package
  import ib_driver64_pkg::*;      // Driver calls back class
  import ib_monitor64_pkg::*;     // Monitor pkg
  //import ib_driver8_pkg::*;      // Driver calls back class
  //import ib_monitor8_pkg::*;     // Monitor pkg  
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
    virtual task pre_tx(ref InternalBusTransaction transaction, integer driverId);
       // Insert transaction to scoreboard
       //$write("Driver %d sends packet:\n", driverId); transaction.display(1);
         
         tScoreboardItem item; 
         
         item.transaction = transaction;
         item.from = 0;
         item.to   = 0;
         this.scoreboard.add(item); // Insert item to scoreboard
       
    endtask

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
        if ( (scoreboard.scoreboard[i].transaction.compare(transaction) == 1 )) begin
              auxRemove = 1;
              scoreboard.remove(i);;
              end
       end
       scoreboard.unlock();
       if (auxRemove == 0) begin
         $write("Unknown transaction received from monitor\n");
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

