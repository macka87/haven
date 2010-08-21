/*
 * ib_monitor_pkg.sv: System Verilog Internal Bus Monitor
 * Copyright (C) 2007 CESNET
 * Author(s): Tomas Malek <tomalek@liberouter.org>
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
 * $Id: ib_monitor_pkg.sv 333 2007-09-05 20:07:59Z xkobie00 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package ib_monitor_pkg;

  import ib_transaction_pkg::*; // Transaction package


  // --------------------------------------------------------------------------
  // -- Internal Bus Monitor Callbacks
  // --------------------------------------------------------------------------
  /* This is a abstract class for creating objects which get benefits from
   * function callback. This object can be used with InternalBusMonitor
   * class. Inheritence from this basic class is neaded for functionality.
   */
  class MonitorCbs;
    
    // -- Class Methods --

    // ------------------------------------------------------------------------
    // Function is called before post_rx is called (modification of transaction)
    virtual task pre_rx(ref InternalBusTransaction transaction, integer monitorId);
      // By default, callback does nothing
    endtask
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    virtual task post_rx(InternalBusTransaction transaction, integer monitorId);
      // By default, callback does nothing
    endtask
  
  endclass : MonitorCbs

  // --------------------------------------------------------------------------
  // -- Internal Bus Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for creating transaction objects from 
   * Internal Bus interface signals. After is transaction received it is sended
   * by callback to processing units (typicaly scoreboard) Unit must be enabled
   * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call.
   */
  class InternalBusMonitor;
    
    // -- Public Class Atributes --

    // -- Private Class Atributes --
    integer monitorId;                       // Monitor identification
    bit     enabled;                         // Monitor is enabled
    MonitorCbs cbs[$];                       // Callbacks list
    virtual iInternalBusLink.rx internalBus; // Internal Bus Interface

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( virtual iInternalBusLink.rx  internalBus,
                   integer monitorId);
      this.enabled     = 0;           // Monitor is disabled by default   
      this.internalBus = internalBus; // Store pointer interface 
      this.monitorId   = monitorId;   // Store driver identifier
      // Setting default values for Internal Bus interface
      internalBus.DST_RDY_N = 0; // Ready even if disabled
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
        run();     // Creating monitor subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Monitor -----------------------------------------------------
    // Disable monitor
    task setDisabled();
      enabled = 0; // Disable monitor, after receiving last transaction
    endtask : setDisabled    
   
    // -- Private Class Methods --

    // -- Random not ready ----------------------------------------------------
    // Disable monitor
    task randomNotReady(bit en);
      if (en) begin
        repeat ($urandom_range(2)) begin
          internalBus.DST_RDY_N = 1;
          @(posedge internalBus.CLK); // Wait for send
        end;
        internalBus.DST_RDY_N = 0;
        end;
    endtask : randomNotReady

    // -- Run Monitor ---------------------------------------------------------
    // Receive transactions and send them for processing by call back
    task run();
      InternalBusTransaction transaction;     
      while (enabled) begin              // Repeat in forewer loop
        transaction = new;               // Create new transaction object
        receiveTransaction(transaction); // Receive Transaction

        if (enabled) begin
          // Call transaction preprocesing, if is available
          foreach (cbs[i]) cbs[i].pre_rx(transaction, monitorId);

          // Call transaction postprocesing, if is available
          foreach (cbs[i]) cbs[i].post_rx(transaction, monitorId);
        end
      end
    endtask : run

    // -- Receive Transaction -------------------------------------------------
    // It receives Internal Bus transaction to tr object
    task receiveTransaction( InternalBusTransaction tr);
      int offset; // Data offset
      bit enNotReady = $urandom_range(8);
      
      do begin
        randomNotReady(enNotReady); // Generate random not ready
        // Wait if not data ready
        if (internalBus.SOP_N || internalBus.SRC_RDY_N)
          @(posedge internalBus.CLK);
        if (!enabled) return;
      end while (internalBus.SOP_N || internalBus.SRC_RDY_N);
      
      tr.length    = internalBus.DATA[11: 0]; // Get length
      tr.tag       = internalBus.DATA[31:16]; // Get tag

      // Get Transaction type
      case (internalBus.DATA[15:12])
         L2LW_TYPE:
            tr.transType = L2LW;
         L2LR_TYPE:
            tr.transType = L2LR;
         L2GW_TYPE:
            tr.transType = L2GW;
         G2LR_TYPE:
            tr.transType = G2LR;
         RDC_TYPE:
            tr.transType = RDC;
         RDCL_TYPE:
            tr.transType = RDCL;
       endcase;
      
      // Store address from first header
      if (tr.transType != L2LW && tr.transType != L2LR) begin
        tr.globalAddr[31: 0] = internalBus.DATA[63:32]; 
        tr.globalAddr[63:32] = 0;
      end
      else
        tr.localAddr = internalBus.DATA[63:32];

      offset = internalBus.DATA[34:32]; // Store data offset

      randomNotReady(enNotReady); // Generate random not ready
      // Wait for second header
      @(posedge internalBus.CLK && internalBus.SRC_RDY_N == 0);

      // Store address from second header
      if (tr.transType != L2LW && tr.transType != L2LR) begin
        tr.globalAddr[63:32] = internalBus.DATA[63:32];  
        tr.localAddr = internalBus.DATA[31:0];
      end
      else begin         
        tr.globalAddr[31 :0]  = internalBus.DATA[31:0];
        tr.globalAddr[63:32]  = 0;
      end
      
      // Process data if available
      if (tr.transType != L2LR && tr.transType != G2LR)
        receiveData(tr, 0); // TODO: IMPORTANT: 0
    endtask : receiveTransaction

    // -- Receive Data --------------------------------------------------------
    // This function receives transaction data
    task receiveData( InternalBusTransaction tr, int offset );
      bit enNotReady = $urandom_range(8);
      // TODO: Add coments, better variable names
      int word64  = (tr.length + offset + 7)/8;
      int low_tr  = 0;
      int low_ib  = 0;
      int high_tr = 7;
      int high_ib = 7;
      tr.data = new[tr.length];

      for (int i=1; i <= word64; i++) begin
        randomNotReady(enNotReady); // Generate random not ready
        @(posedge internalBus.CLK && internalBus.SRC_RDY_N == 0);
        // first word
        if (i == 1) 
          low_ib = offset;              
        else
          low_ib = 0;
          
        // last word
        if (i == word64) begin        
          high_tr -= (8 - ((tr.length) % 8));
          high_ib  = ( ((tr.length + offset) - 1) % 8); 
          if (internalBus.EOP_N == 1) begin
            $write("Error: Monitor %d receive transaction with wrong length", monitorId);
            $stop;
          end;
        end
               
        // One 64-bit copying
        for (low_ib = low_ib; low_ib <= high_ib ; low_ib++) begin 
          logic [7:0] wbyte = 0;
          for (int j=0; j<8; j++)
            wbyte[j] = internalBus.DATA[low_ib*8 + j]; 
          tr.data[low_tr++] = wbyte;
        end          
  
        high_tr += 8;     
      end


    endtask : receiveData  
  endclass : InternalBusMonitor

endpackage : ib_monitor_pkg
