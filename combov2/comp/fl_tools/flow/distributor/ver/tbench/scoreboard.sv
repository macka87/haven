/*
 * scoreboard.sv: Frame Link Scoreboard
 * Copyright (C) 2009 CESNET
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
import sv_fl_pkg::*;
import math_pkg::*;
  
  // --------------------------------------------------------------------------
  // -- Frame Link Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardDriverCbs #(int pFlows = 4, int pDefaultIfc = 0, 
                              int pInumOffset = 0) extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(1) sc_table[] = new[pFlows];
    bit [log2(pFlows)-1:0] outputIfc = pDefaultIfc;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (TransactionTable #(1) sc_table[]);
      this.sc_table = sc_table;
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
      FrameLinkTransaction tr;
      string trLabel;
      $cast(tr,transaction);

      // If pMarkOffset is not bigger than part size, get mark from correct 
      // bits, else use default interface
      if (!(pInumOffset+log2(pFlows) > tr.data[0].size*8))
        for(int i=0; i<log2(pFlows); i++)
          outputIfc[i] = tr.data[0][(pInumOffset+i)/8][(pInumOffset+i)%8];

      // Add transaction to tr table
      sc_table[outputIfc].add(transaction);

      `ifdef DEBUG
        $swrite(trLabel,"Output interface: %0d", outputIfc);
        transaction.display(trLabel);  
      `endif  
    endtask

   endclass : ScoreboardDriverCbs


  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardMonitorCbs #(int pFlows = 4) extends MonitorCbs;
    
    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(1) sc_table[] = new[pFlows];
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (TransactionTable #(1) sc_table[]);
      this.sc_table = sc_table;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    
    virtual task post_rx(Transaction transaction, string inst);
      bit status=0;
      // Gets number of transaction table from instance name
      int i;
      string tableLabel;
         
      for(i=0; i< pFlows; i++) begin
        string monitorLabel;
        $swrite(monitorLabel, "Monitor %0d", i);
        if (monitorLabel == inst) break;
      end  
      
      sc_table[i].remove(transaction, status);
      if (status==0)begin
         $swrite(tableLabel, "TX%0d", i);
         $write("Unknown transaction received from monitor %d\n", inst);
         transaction.display(); 
         sc_table[i].display(.inst(tableLabel));
         $stop;
       end
    endtask
 
  endclass : ScoreboardMonitorCbs

  // -- Constructor ---------------------------------------------------------
  // Create a class 
  // --------------------------------------------------------------------------
  // -- Scoreboard
  // --------------------------------------------------------------------------
  class Scoreboard #(int pFlows = 4, int pDefaultIfc = 0, int pInumOffset = 0);

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(1) scoreTable[];
    ScoreboardMonitorCbs #(pFlows) monitorCbs;
    ScoreboardDriverCbs  #(pFlows,pDefaultIfc,pInumOffset) driverCbs;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      this.scoreTable = new[pFlows];
      foreach(this.scoreTable[i])
        this.scoreTable[i] = new();

      this.monitorCbs = new(scoreTable);
      this.driverCbs  = new(scoreTable);
    endfunction

    // -- Display -------------------------------------------------------------
    // Create a class 
    task display();
      string tableLabel;

      foreach(this.scoreTable[i]) begin
        $swrite(tableLabel, "TX%0d", i);
        scoreTable[i].display(.inst(tableLabel));
      end  
    endtask
  
  endclass : Scoreboard

