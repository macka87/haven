/*
 * scoreboard.sv: Frame Link Scoreboard
 * Copyright (C) 2009 CESNET
 * Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz>
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
 * $Id:
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import test_pkg::*;
import sv_fl_pkg::*;

`include "ext_transaction.sv"

  // --------------------------------------------------------------------------
  // -- Frame Link Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardDriverCbs #(int DATA_WIDTH = 32,
                              int PART = 0,
                              int EXT_OFFSET = 5,
                              int EXT_SIZE = 5,
                              int CUT_OFFSET = 1,
                              int CUT_SIZE = 1,
                              int PART_COUNT = 3
                             ) extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable sc_table, ext_table;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (TransactionTable sc_table, TransactionTable ext_table);
      this.sc_table = sc_table;
      this.ext_table = ext_table;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called after transaction is sended 
    
    virtual task post_tx(Transaction transaction, string inst);
       // transaction.display("DRIVER");
       FrameLinkTransaction tr;
       ExtDataTransaction ext;
       const int bpword = DATA_WIDTH/8; //bytes per word
       byte unsigned data[];
       int whole_part = 0;

       ext = new;

       $cast(tr,transaction);

       // Extracting data
       if (PART < tr.packetCount)
       begin
          ext.op_size = tr.data[PART].size;
          if (((tr.data[PART].size - 1) / bpword) >= EXT_OFFSET / bpword)
          begin
             //there is enough words to start extraction but we must check if there is enough data also
             //extraction can start in this part
             if (tr.data[PART].size >= EXT_OFFSET+EXT_SIZE)
             begin
                //extraction can be done completely
                ext.ext_data = new[EXT_SIZE];
                for (int i = 0; i < EXT_SIZE; i++)
                begin
                   ext.ext_data[i] = tr.data[PART][EXT_OFFSET + i];
                end
                ext.ext_done = 1;
                ext.ext_err = 0;
             end
             else
             begin
                //extraction will be interrupted due to lack of data but we must extract as much data as we can
                if (tr.data[PART].size - EXT_OFFSET - 1 > 0)
                begin
                   ext.ext_data = new[tr.data[PART].size - EXT_OFFSET - 1];
                   for (int i = EXT_OFFSET; i < tr.data[PART].size; i++)
                   begin
                      ext.ext_data[i-EXT_OFFSET] = tr.data[PART][i];
                   end
                   ext.op_size = tr.data[PART].size;
                end
                ext.ext_done = 1;
                ext.ext_err = 1;
             end

             ext_table.add(ext);
          end
          else
          begin
             //extraction will not start in this part due to lack of data
             ext.ext_done = 0;
             ext.ext_err = 0;
          end
       end
       else
       begin
          //extraction will not start in this frame due to lack of parts
          ext.ext_done = 0;
          ext.ext_err = 0;
       end


       // Cutting data
       if (CUT_SIZE > 0)
       begin
          if (PART < tr.packetCount)
          begin
             if (tr.data[PART].size > CUT_OFFSET*bpword)
             begin
             //cutting in progress - whole words only
	        if (tr.data[PART].size - bpword*(CUT_OFFSET + CUT_SIZE) <= 0) 
	        begin
                //not enough data in particular part => cut whole part or cutting will be interrupted due to lack of data
                   if (CUT_OFFSET == 0)
                   begin
	           //cut whole part
	              for (int i = PART; i < PART_COUNT-1; i++)
	              begin
                         tr.data[i] = new[tr.data[i+1].size](tr.data[i+1]);  //move rest of data one part up
	              end
	              tr.data[PART_COUNT-1].delete();
                      tr.packetCount = PART_COUNT-1;
	           end
                   else
                   begin
                   //cutting will be interrupted due to lack of data
                      tr.data[PART] = new[CUT_OFFSET*bpword](tr.data[PART]);
                   end
                end
	        else
	        begin
                //enough data in particular part => cut specific words in a part
	           for (int i = CUT_OFFSET*bpword; i < tr.data[PART].size - CUT_SIZE*bpword; i = i + bpword)
                   begin
                      for (int j = 0; j < bpword; j++)
                      begin
	                 tr.data[PART][i+j] = tr.data[PART][i+j+CUT_SIZE*bpword];
                      end
                   end
                   if ((tr.data[PART].size % bpword != 0) && (tr.data[PART].size - CUT_OFFSET*bpword < bpword))
                   begin
                      tr.data[PART] = new[tr.data[PART].size-(tr.data[PART].size % bpword)](tr.data[PART]);
                   end
                   else
                   begin
                      tr.data[PART] = new[tr.data[PART].size-CUT_SIZE*bpword](tr.data[PART]);
                   end
                end
             end
          end
       end

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

  class ExtScoreboardMonitorCbs extends MonitorCbs;

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
      // transaction.display("EXT_MONITOR");
      sc_table.remove(transaction, status);
      if (status==0)begin
         $write("Unknown transaction received from monitor %d\n", inst);
         transaction.display();
         sc_table.display();
         $stop;
       end;
    endtask


  endclass : ExtScoreboardMonitorCbs

  // -- Constructor ---------------------------------------------------------
  // Create a class 
  // --------------------------------------------------------------------------
  // -- Scoreboard
  // --------------------------------------------------------------------------
  class Scoreboard #(int DATA_WIDTH = 32,
                     int PART = 0,
                     int EXT_OFFSET = 5,
                     int EXT_SIZE = 5,
                     int CUT_OFFSET = 1,
                     int CUT_SIZE = 1,
                     int PART_COUNT = 3);

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable     scoreTable;
    ScoreboardMonitorCbs monitorCbs;
    ScoreboardDriverCbs  #(DATA_WIDTH, PART, EXT_OFFSET, EXT_SIZE, CUT_OFFSET, CUT_SIZE, PART_COUNT) driverCbs;


    TransactionTable     extTable;
    ExtScoreboardMonitorCbs ext_monitorCbs;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      this.scoreTable = new;
      this.extTable   = new;
      this.monitorCbs = new(scoreTable);
      this.driverCbs  = new(scoreTable, extTable);
      this.ext_monitorCbs = new(extTable);
    endfunction

    // -- Display -------------------------------------------------------------
    // Create a class 
    task display();
      scoreTable.display();
    endtask
  
  endclass : Scoreboard

