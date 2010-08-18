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
import test_pkg::*;
import sv_fl_pkg::*;
  
  // --------------------------------------------------------------------------
  // -- Frame Link Driver Callbacks
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
    // Function is called after is transaction sended 
    
    virtual task post_tx(Transaction transaction, string inst);
       // transaction.display("DRIVER");
       FrameLinkTransaction tr;
       byte unsigned data[];
       bit[63:0] indata;
       indata = 'd6418;
       $cast(tr,transaction);
       data = new[tr.data[0].size + 8];
       data[0] = indata[7:0];
       data[1] = indata[15:8];
       data[2] = indata[23:16];
       data[3] = indata[31:24];
       data[4] = indata[39:32];
       data[5] = indata[47:40];
       data[6] = indata[55:48];
       data[7] = indata[63:56];
       for (int i = 8 ;i <= (tr.data[0].size + 7); i++)
         data[i] = tr.data[0][i-8];
       tr.data[0] = data;
       sc_table.add(tr);
    endtask

   endclass : ScoreboardDriverCbs


  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
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
  class Scoreboard;
    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable     scoreTable;
    ScoreboardMonitorCbs monitorCbs;
    ScoreboardDriverCbs  driverCbs;

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
  
  endclass : Scoreboard

