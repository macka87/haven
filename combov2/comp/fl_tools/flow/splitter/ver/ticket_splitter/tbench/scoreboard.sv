/*
 * scoreboard.sv: Frame Link Scoreboard
 * Copyright (C) 2007 CESNET
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
import sv_fl_pkg::*;

  // --------------------------------------------------------------------------
  // -- Control Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardCtrlDriverCbs #(pDataSize = 8) extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    // Applicated marks queue
    bit markQue[$][pDataSize-1:0];

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();

    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called before is transaction sended 
    // Allow modify transaction before is sended
    virtual task pre_tx(ref Transaction transaction, string inst);
    
    endtask
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction sended 
    
    virtual task post_tx(Transaction transaction, string inst);
      ControlTransaction tr;

      $cast(tr, transaction);

      markQue.push_back(tr.data);
    endtask

   endclass : ScoreboardCtrlDriverCbs
  
  // --------------------------------------------------------------------------
  // -- Frame Link Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardFlDriverCbs #(behav = 1, pDataSize = 8) extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable        #(behav)     sc_table;
    ScoreboardCtrlDriverCbs #(pDataSize) ctrlDriverCbs;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (TransactionTable #(behav) sc_table,
                  ScoreboardCtrlDriverCbs #(pDataSize) ctrlDriverCbs
                 );
      this.sc_table      = sc_table;
      this.ctrlDriverCbs = ctrlDriverCbs;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called before is transaction sended 
    // Allow modify transaction before is sended
    virtual task pre_tx(ref Transaction transaction, string inst);
    //   FrameLinkTransaction tr;
    //   $cast(tr,transaction);
    
    // Example - set first byte of first packet in each frame to zero   
    //   tr.data[0][0]=0;
    endtask
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction sended 
    
    virtual task post_tx(Transaction transaction, string inst);
      FrameLinkTicketTransaction tr;
//      bit[pDataSize-1:0] aux = ctrlDriverCbs.markQue.pop_front();

      $cast(tr, transaction);

      tr.ticketData = new[pDataSize];
//      for (int i=0; i<pDataSize; i++)
//        tr.ticketData[i] = aux;
      tr.ticketData = ctrlDriverCbs.markQue.pop_front();

      sc_table.add(tr);
    endtask

   endclass : ScoreboardFlDriverCbs


  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardMonitorCbs #(behav = 1) extends MonitorCbs;
    
    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable        #(behav)     sc_table;
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (TransactionTable #(behav) sc_table);
      this.sc_table      = sc_table;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    
    virtual task post_rx(Transaction transaction, string inst);
      bit status=0;

      // transaction.display("MONITOR");
      sc_table.remove(transaction, status);
      if (status==0)begin
         $write("Unknown transaction received from monitor %d\n", inst);
         transaction.display(); 
         sc_table.display();
         $stop;
       end;
    endtask

 
  endclass : ScoreboardMonitorCbs

  // -- Constructor ---------------------------------------------------------
  // Create a class 
  // --------------------------------------------------------------------------
  // -- Scoreboard
  // --------------------------------------------------------------------------
  class Scoreboard #(behav = 1, pDataSize = 8);
    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable         #(behav)           scoreTable;
    ScoreboardMonitorCbs     #(behav)           monitorCbs;
    ScoreboardFlDriverCbs    #(behav,pDataSize) flDriverCbs;
    ScoreboardCtrlDriverCbs  #(pDataSize)       ctrlDriverCbs;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      this.scoreTable     = new();
      this.ctrlDriverCbs  = new();
      this.flDriverCbs    = new(scoreTable,ctrlDriverCbs);
      this.monitorCbs     = new(scoreTable);
    endfunction

    // -- Display -------------------------------------------------------------
    // Create a class 
    task display();
      scoreTable.display();
    endtask
  
  endclass : Scoreboard

