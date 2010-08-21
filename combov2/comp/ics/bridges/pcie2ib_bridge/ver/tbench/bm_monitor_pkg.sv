//
// bm_monitor_pkg.sv: System Verilog Bus Master Monitor
// Copyright (C) 2007 CESNET
// Author(s): Tomas Malek <tomalek@liberouter.org>
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in
//    the documentation and/or other materials provided with the
//    distribution.
// 3. Neither the name of the Company nor the names of its contributors
//    may be used to endorse or promote products derived from this
//    software without specific prior written permission.
//
// This software is provided ``as is'', and any express or implied
// warranties, including, but not limited to, the implied warranties of
// merchantability and fitness for a particular purpose are disclaimed.
// In no event shall the company or contributors be liable for any
// direct, indirect, incidental, special, exemplary, or consequential
// damages (including, but not limited to, procurement of substitute
// goods or services; loss of use, data, or profits; or business
// interruption) however caused and on any theory of liability, whether
// in contract, strict liability, or tort (including negligence or
// otherwise) arising in any way out of the use of this software, even
// if advised of the possibility of such damage.
//
// $Id: bm_monitor_pkg.sv 688 2007-10-19 16:11:56Z tomalek $
//

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package bm_monitor_pkg;

  import bm_transaction_pkg::*; // Transaction package


  // --------------------------------------------------------------------------
  // -- Bus Master Monitor Callbacks
  // --------------------------------------------------------------------------
  /* This is a abstract class for creating objects which get benefits from
   * function callback. This object can be used with BusMasterMonitor
   * class. Inheritence from this basic class is neaded for functionality.
   */
  class BmMonitorCbs;
    
    // -- Class Methods --

    // ------------------------------------------------------------------------
    // Function is called before post_rx is called (modification of transaction)
    virtual task pre_rx(ref BusMasterTransaction transaction);
      // By default, callback does nothing
    endtask
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    virtual task post_rx(BusMasterTransaction transaction);
      // By default, callback does nothing
    endtask
  
  endclass : BmMonitorCbs

  // --------------------------------------------------------------------------
  // -- Bus Master Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for creating transaction objects from 
   * Internal Bus interface signals. After is transaction received it is sended
   * by callback to processing units (typicaly scoreboard) Unit must be enabled
   * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call.
   */
  class BusMasterMonitor;
    
    // -- Public Class Atributes --

    // -- Private Class Atributes --
    bit     enabled;                         // Monitor is enabled
    BmMonitorCbs cbs[$];                     // Callbacks list
    virtual iIbBm64.monitor BM;              // Bus Master Interface 

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( virtual iIbBm64.monitor BM );
      this.enabled = 0;           // Monitor is disabled by default   
      this.BM      = BM; // Store pointer interface 
    endfunction

    // -- Set Callbacks -------------------------------------------------------
    // Put callback object into List 
    function void setCallbacks(BmMonitorCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks

    // -- Enable Monitor ------------------------------------------------------
    // Enable monitor and runs monitor process
    task setEnabled();
      enabled = 1; // Monitor Enabling
      fork         
        run();     // Creating monitor subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Monitor -----------------------------------------------------
    // Disable monitor
    task setDisabled();
      enabled = 0; // Disable monitor, after receiving last transaction
    endtask : setDisabled    
   
    // -- Private Class Methods --

    // -- Run Monitor ---------------------------------------------------------
    // Receive transactions and send them for processing by call back
    task run();
      BusMasterTransaction transaction;     
      while (enabled) begin              // Repeat in forewer loop
        transaction = new;               // Create new transaction object
        receiveTransaction(transaction); // Receive Transaction
       
        if (enabled) begin                                                           
          // Call transaction preprocesing, if is available
          foreach (cbs[i]) cbs[i].pre_rx(transaction);

          // Call transaction postprocesing, if is available
          foreach (cbs[i]) cbs[i].post_rx(transaction);
        end
      end
    endtask : run

    // -- Receive Transaction -------------------------------------------------
    // It receives Bus Master transaction to tr object
    task receiveTransaction( BusMasterTransaction tr);
      bit done;

      // wait until OP_DONE
      do begin
        @(negedge BM.CLK);
        done = BM.OP_DONE;        
        if (!enabled) return;
      end while (!done);

      // store tag
      tr.tag = BM.OP_TAG;

      // wait on positive edge
      @(posedge BM.CLK);
      
    endtask : receiveTransaction

  endclass : BusMasterMonitor

endpackage : bm_monitor_pkg



