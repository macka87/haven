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
  import dpi_scoreboard_pkg::*;
  
  // --------------------------------------------------------------------------
  // -- Frame Link Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardDriverCbs extends DriverCbs;
   
    // ------------------------------------------------------------------------
    // Function is called after is transaction sended 
    virtual task post_tx(Transaction transaction, string inst);
      tFlTransactionInfo info;
      FrameLinkTransaction tr;
      int last;
      $cast(tr, transaction);

      info.stream_id   = tr.stream_id;
      info.scenario_id = tr.scenario_id;
      info.data_id     = tr.data_id;
      info.inst        = inst;
      for (int i=0; i < tr.packetCount; i++) begin
        last = (i==tr.packetCount-1);
        assert(c_flPostTx(info,last,tr.data[i]));
      end
    endtask

   endclass : ScoreboardDriverCbs


  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardMonitorCbs extends MonitorCbs;
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    virtual task post_rx(Transaction transaction, string inst);
      tFlTransactionInfo info;
      FrameLinkTransaction tr;
      int last;
      $cast(tr, transaction);

      info.stream_id   = tr.stream_id;
      info.scenario_id = tr.scenario_id;
      info.data_id     = tr.data_id;
      info.inst        = inst;
      for (int i=0; i < tr.packetCount; i++) begin
        last = (i==tr.packetCount-1);
        assert(c_flPostRx(info,last,tr.data[i]));
      end
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
    ScoreboardMonitorCbs monitorCbs;
    ScoreboardDriverCbs  driverCbs;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      this.monitorCbs = new;
      this.driverCbs  = new;
    endfunction

     // -- Display -------------------------------------------------------------
    // Create a class 
    task display();
      c_display();
    endtask 

  endclass : Scoreboard

