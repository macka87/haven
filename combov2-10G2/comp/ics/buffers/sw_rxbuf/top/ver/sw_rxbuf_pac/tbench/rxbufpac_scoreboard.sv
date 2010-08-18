/*
 * rxbuf_scoreboard.sv: SW RX Buffer Scoreboard
 * Copyright (C) 2008 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
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
  // -- SW RX Buffer Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardDriverCbs extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable sc_table;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (TransactionTable sc_table);
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
       sc_table.add(transaction);
    endtask

   endclass : ScoreboardDriverCbs


  // --------------------------------------------------------------------------
  // -- SW RX Buffer Monitor Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardMonitorCbs extends MonitorCbs;
    
    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable sc_table;
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (TransactionTable sc_table);
      this.sc_table = sc_table;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    
    virtual task post_rx(Transaction transaction, string inst);
      bit status=0;
      sc_table.remove(transaction, status);
      if (status==0)begin
         $write("Unknown transaction received from monitor %d\n", inst);
         $timeformat(-9, 3, " ns", 8);
         $write("Time: %t\n", $time);
         transaction.display(); 
         sc_table.display();
         $stop;
       end;
    endtask

 
  endclass : ScoreboardMonitorCbs

  // --------------------------------------------------------------------------
  // -- SW RX Buffer Scoreboard
  // --------------------------------------------------------------------------
  class SwRxBufPacScoreboard;
    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable     scoreTable;
    ScoreboardMonitorCbs monitorCbs;
    ScoreboardDriverCbs  driverCbs;
    

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      this.scoreTable   = new;
      this.monitorCbs   = new(scoreTable);
      this.driverCbs    = new(scoreTable);
    endfunction

    // -- Display -------------------------------------------------------------
    // Create a class 
    task display();
      scoreTable.display();
    endtask
  
  endclass : SwRxBufPacScoreboard

