/*
 * bm_monitor.sv: Bus Master Done Monitor
 * Copyright (C) 2009 CESNET
 * Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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
 * $Id: bm_monitor.sv 7915 2009-03-31 08:08:01Z washek $
 *
 * TODO:
 *
 */ 
  
package bm_monitor_pkg;

  import sv_common_pkg::*;           // Import SV common classes
  import done_transaction_pkg::*;    // Done transaction
  
  // --------------------------------------------------------------------------
  // -- Bus Mater Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for creating transaction objects from 
   * Bus Master Done interface signals. After a transaction is received it is 
   * sent by callback to processing units (typicaly scoreboard) Unit must be 
   * enabled by "setEnable()" function call. Monitoring can be stoped by 
   * "setDisable()" function call.
   */
  class IbBusMasterMonitor;
    
    // -- Private Class Atributes --
    string  inst;                     // Monitor identification
    bit     enabled;                  // Monitor is enabled
    bit     busy;                     // Monitor is receiving transaction
    MonitorCbs         cbs[$];        // Callbacks list
    virtual iIbEndpointBMDone.tb bm;  // Done interface
    
        
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst, virtual iIbEndpointBMDone.tb bm);
      this.enabled     = 0;           // Monitor is disabled by default
      this.busy        = 0;   
      this.bm          = bm;          // Store pointer interface 
      this.inst        = inst;        // Store driver identifier
    endfunction

    // -- Set Callbacks -------------------------------------------------------
    // Put callback object into List 
    function void setCallbacks(MonitorCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks

    // -- Enable Monitor ------------------------------------------------------
    // Enable monitor and runs monitor process
    task setEnabled();
      enabled = 1; // Monitor Enabling
      fork         
        run();       // Creating monitor subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Monitor -----------------------------------------------------
    // Disable monitor
    task setDisabled();
      enabled = 0; // Disable monitor, after receiving last transaction
    endtask : setDisabled 
    
    // -- Run Monitor ---------------------------------------------------------
    // Receive tags and send them for processing by callback
    task run();
      DoneTransaction tr; 
      while (enabled) begin    // Repeat in forewer loop
        tr = new;              // Create new transaction object
        receiveTag(tr);        // Receive operation tag
        @(bm.cb);
        if (enabled) begin
          // Send tag to scoreboard by calling callbacks.
          foreach (cbs[i]) cbs[i].post_rx(tr, inst);
        end
      end
    endtask : run
    
    // -- Receive Transaction -------------------------------------------------
    // It receives tags from Done interface
    task receiveTag(DoneTransaction tr);
      
      busy = 0;
      
      //Wait for TAG_VLD
      while (bm.cb.TAG_VLD !== 1) begin
         @(bm.cb);
         if (!enabled) return;
      end
      
      busy = 1;
      
      tr.tag = bm.cb.TAG;

    endtask : receiveTag
    
  endclass : IbBusMasterMonitor

endpackage : bm_monitor_pkg;
