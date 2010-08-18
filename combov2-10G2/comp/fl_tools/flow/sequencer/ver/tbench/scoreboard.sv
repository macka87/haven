/*
 * scoreboard.sv: Frame Link Scoreboard
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
import sv_fl_pkg::*;
  
  // --------------------------------------------------------------------------
  // -- Frame Link Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardDriverCbs #(int parts=3, int ticketPart=0, int ticketSize=2, int ticket_offset=0) extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(1) sc_table;
		int packetCounter;
    
    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (TransactionTable #(1) sc_table);
      this.sc_table = sc_table;
			this.packetCounter = 0;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called before is transaction sended 
    // Allow modify transaction before is sended
    
    virtual task pre_tx(ref Transaction transaction, string inst);
       FrameLinkTransaction tr;                  // FrameLink transaction
       static bit[ticketSize*8-1:0] counter = 0; // ticket counter  
                   
       $cast(tr,transaction);

       // add transaction to transaction table
       sc_table.add(tr.copy);

       // enlarge packet to make space for ticket
       tr.data[ticketPart] = new[ticketSize+tr.data[ticketPart].size](tr.data[ticketPart]);
                          
       // shift data
       for (int i=tr.data[ticketPart].size-1; i>=ticketSize+ticket_offset; i--)  
         tr.data[ticketPart][i] = tr.data[ticketPart][i-ticketSize];
       
       // add ticket
       for (int i=0; i<ticketSize*8; i++)
         tr.data[ticketPart][ticket_offset+i/8][i%8] = counter[i]; 

       counter++; // increment ticket counter

       //tr.display("SCOREBOARD s TICKETOM");
			 $write(this.packetCounter);
			 $write("\n");
			 this.packetCounter++;
    endtask
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction sended 
    virtual task post_tx(Transaction transaction, string inst);

    endtask

   endclass : ScoreboardDriverCbs


  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardMonitorCbs extends MonitorCbs;
    
    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(1) sc_table;
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (TransactionTable #(1) sc_table);
      this.sc_table = sc_table;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    
    virtual task post_rx(Transaction transaction, string inst);
      bit status=0;
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
  class Scoreboard #(int parts=3, int ticketPart=0, int ticketSize=2, int ticket_offset=0);
    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(1) scoreTable;
    ScoreboardMonitorCbs  monitorCbs;
    ScoreboardDriverCbs #(parts,ticketPart,ticketSize,ticket_offset)   driverCbs;

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

