/*
 * scoreboard.sv: TX DMA Controller Scoreboard
 * Copyright (C) 2008 CESNET
 * Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
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
  
  // --------------------------------------------------------------------------
  // -- Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardDriverCbs #(int pFlows=2, int behav=1) extends DriverCbs; 

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(behav) sc_table[] = new [pFlows];

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (TransactionTable #(behav) sc_table[]);
      this.sc_table = sc_table;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called before is transaction sended 
    // Allow modify transaction before is sended
    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction sended 
    
    virtual task post_tx(Transaction transaction, string inst);
       FrameLinkTransaction tr;
      
       $cast(tr, transaction);
       sc_table[tr.ifcNo].add(transaction);
    endtask

   endclass : ScoreboardDriverCbs


  // --------------------------------------------------------------------------
  // -- Monitor Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardMonitorCbs #(int pFlows=2, int behav=1) extends MonitorCbs; 
    
    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(behav) sc_table[] = new[pFlows];
    
    // -------------------
    // -- Class Methods --
    // -------------------
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (TransactionTable #(behav) sc_table[]);
      this.sc_table = sc_table;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    
    virtual task post_rx(Transaction transaction, string inst);
      FrameLinkTransaction tr;
      bit status=0;
           
      $cast(tr, transaction);
         
      sc_table[tr.ifcNo].remove(transaction, status);
      if (status==0)begin
        $write("Unknown transaction received from monitor %d\n", inst);
        $timeformat(-9, 3, " ns", 8);
        $write("Time: %t\n", $time);
        transaction.display(); 
        sc_table[tr.ifcNo].display();
        $stop;
      end;
    endtask
 
  endclass : ScoreboardMonitorCbs

  // --------------------------------------------------------------------------
  // -- Scoreboard
  // --------------------------------------------------------------------------
  class Scoreboard #(int pFlows=2, int behav=1);
    
    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable     #(behav)           scoreTable[] = new[pFlows];
    ScoreboardMonitorCbs #(pFlows, behav)   monitorCbs;
    ScoreboardDriverCbs  #(pFlows, behav)   driverCbs;

    // -------------------
    // -- Class Methods --
    // -------------------
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      for(int i=0;i<pFlows;i++) begin
        this.scoreTable[i]= new; 
      end
      
      this.monitorCbs = new(scoreTable);
      this.driverCbs  = new(scoreTable);
    endfunction

    // -- Display -------------------------------------------------------------
    // Create a class 
    task display();
      for (int i=0; i<pFlows; i++)
        scoreTable[i].display();
    endtask
  
  endclass : Scoreboard

