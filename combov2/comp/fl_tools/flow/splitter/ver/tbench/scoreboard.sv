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
  // -- Frame Link Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardDriverCbs extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(0) sc_table;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (TransactionTable #(0) sc_table);
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
       // transaction.display("DRIVER");
       sc_table.add(transaction);
    endtask

   endclass : ScoreboardDriverCbs


  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardMonitorCbs#(int pOutputCount = 1) extends MonitorCbs;
    
    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(0) sc_table;
    bit pktCntCheck          = 0;
    int pktCnt[pOutputCount] = '{default: 0};
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (TransactionTable #(0) sc_table);
      this.sc_table = sc_table;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    virtual task post_rx(Transaction transaction, string inst);
      bit status=0;

      for(int i=0; i< pOutputCount; i++) begin
        string monitorLabel;
        $swrite(monitorLabel, "Monitor %0d", i);
        if (monitorLabel == inst) begin
          pktCnt[i]++;
          if (pktCntCheck)
            for (int j=0; j< pOutputCount-1; j++) begin
              assert ((pktCnt[j]-1 == pktCnt[j+1]) || 
                      (pktCnt[j]   == pktCnt[j+1]) ||
                      (pktCnt[j]+1 == pktCnt[j+1]))
              else begin
                $error("Number of packets received by interface %0d is too high", j);
                display();
                $stop;
              end  
            end
          break;
        end
      end  
      
      // transaction.display("MONITOR");
      sc_table.remove(transaction, status);
      if (status==0)begin
         $write("Unknown transaction received from monitor %d\n", inst);
         transaction.display(); 
         sc_table.display();
         $stop;
       end;
    endtask

    // ------------------------------------------------------------------------
    // Function displays number of packet received on each interface
    function void display;
      $write("---------------------------------------------\n");
      $write("Number of packets received on each interface:\n");
      for(int i=0; i < pOutputCount; i++)
        $write("Interface %0d: %0d pkts\n",i,pktCnt[i]);
      $write("---------------------------------------------\n");
    endfunction: display
 
    // -- Enable Packet Count Check -------------------------------------------
    // Enables packet count checking 
    task enablePktCntCheck();
      pktCntCheck = 1;
    endtask: enablePktCntCheck
  
    // -- Disable Packet Count Check ------------------------------------------
    // Disables packet count checking 
    task disablePktCntCheck();
      pktCntCheck = 0;
    endtask: disablePktCntCheck
  
  endclass : ScoreboardMonitorCbs

  // -- Constructor ---------------------------------------------------------
  // Create a class 
  // --------------------------------------------------------------------------
  // -- Scoreboard
  // --------------------------------------------------------------------------
  class Scoreboard#(int pOutputCount = 1);
    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable     #(0)             scoreTable;
    ScoreboardMonitorCbs #(pOutputCount)  monitorCbs;
    ScoreboardDriverCbs                   driverCbs;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      this.scoreTable = new;
      this.monitorCbs = new(scoreTable);
      this.driverCbs  = new(scoreTable);
    endfunction

    // -- Display -------------------------------------------------------------
    // Display transaction table 
    task display();
      monitorCbs.display();
      scoreTable.display();
    endtask
  
    // -- Enable Packet Count Check -------------------------------------------
    // Enables packet count checking 
    task enablePktCntCheck();
      monitorCbs.enablePktCntCheck();
    endtask: enablePktCntCheck
  
    // -- Disable Packet Count Check ------------------------------------------
    // Disables packet count checking 
    task disablePktCntCheck();
      monitorCbs.disablePktCntCheck();
    endtask: disablePktCntCheck
  
  endclass : Scoreboard

