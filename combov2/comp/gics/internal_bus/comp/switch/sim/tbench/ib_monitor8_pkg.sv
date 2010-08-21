/*
 * ib_monitor_pkg.sv: System Verilog Internal Bus Monitor
 * Copyright (C) 2008 CESNET
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
 * $Id: ib_monitor8_pkg.sv 1366 2008-02-18 15:26:54Z tomalek $
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
    virtual iIB.rx internalBus;            // Internal Bus Interface

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( virtual iIB.rx  internalBus,
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
        $write("M%0x: ",monitorId);
        transaction.display(1);          // Display transaction

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
      bit sopInactive;

      // Wait for START OF PACKET -------------------------
      do begin
        randomNotReady(enNotReady); 
        @(negedge internalBus.CLK);
        sopInactive = internalBus.SOF_N || internalBus.SRC_RDY_N;
        if (sopInactive) @(posedge internalBus.CLK);
        if (!enabled) return;
      end while (sopInactive); 
            
      // 7:0 DATA -----------------------------------------
      case (internalBus.DATA[3:0])
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
      
      tr.length[3:0] = internalBus.DATA[ 7: 4]; // Get length

      // 7:0 WAIT -----------------------------------------
      @(posedge internalBus.CLK);
      randomNotReady(enNotReady); 
      do begin
       @(negedge internalBus.CLK);
      end
      while (internalBus.SRC_RDY_N == 1);      

      // 15:8 DATA ----------------------------------------
      tr.length[11:4] = internalBus.DATA[ 7: 0]; // Get length

      // 15:8 WAIT ----------------------------------------
      @(posedge internalBus.CLK);
      randomNotReady(enNotReady); 
      do begin
       @(negedge internalBus.CLK);
      end
      while (internalBus.SRC_RDY_N == 1);            

      // 23:16 DATA ---------------------------------------
      tr.tag[7:0] = internalBus.DATA[7:0]; // Get tag

      // 23:16 WAIT ---------------------------------------
      @(posedge internalBus.CLK);
      randomNotReady(enNotReady); 
      do begin
       @(negedge internalBus.CLK);
      end
      while (internalBus.SRC_RDY_N == 1);                  

      // 31:24 DATA ---------------------------------------

      // 31:24 WAIT ---------------------------------------
      @(posedge internalBus.CLK);
      randomNotReady(enNotReady); 
      do begin
       @(negedge internalBus.CLK);
      end
      while (internalBus.SRC_RDY_N == 1);                        
 
      // 39:32 DATA ---------------------------------------      
      if (tr.transType != L2LW && tr.transType != L2LR) begin
        tr.globalAddr[7: 0] = internalBus.DATA[7:0]; 
        tr.globalAddr[63:32] = 0;
      end
      else
        tr.localAddr[7:0] = internalBus.DATA[7:0];

      offset = internalBus.DATA[2:0]; // Store data offset

      // 39:32 WAIT ---------------------------------------
      @(posedge internalBus.CLK);
      randomNotReady(enNotReady); 
      do begin
       @(negedge internalBus.CLK);
      end
      while (internalBus.SRC_RDY_N == 1);

      // 47:40 DATA ---------------------------------------      
      if (tr.transType != L2LW && tr.transType != L2LR) begin
        tr.globalAddr[15: 8] = internalBus.DATA[7:0]; 
        tr.globalAddr[63:32] = 0;
      end
      else
        tr.localAddr[15:8] = internalBus.DATA[7:0];

      // 47:40 WAIT ---------------------------------------
      @(posedge internalBus.CLK);
      randomNotReady(enNotReady); 
      do begin
       @(negedge internalBus.CLK);
      end
      while (internalBus.SRC_RDY_N == 1);                               

      // 55:48 DATA ---------------------------------------      
      if (tr.transType != L2LW && tr.transType != L2LR) begin
        tr.globalAddr[23: 16] = internalBus.DATA[7:0]; 
        tr.globalAddr[63:32] = 0;
      end
      else
        tr.localAddr[23:16] = internalBus.DATA[7:0];

      // 55:48 WAIT ---------------------------------------
      @(posedge internalBus.CLK);
      randomNotReady(enNotReady); 
      do begin
       @(negedge internalBus.CLK);
      end
      while (internalBus.SRC_RDY_N == 1);                                     

      // 63:56 DATA ---------------------------------------      
      if (tr.transType != L2LW && tr.transType != L2LR) begin
        tr.globalAddr[31: 24] = internalBus.DATA[7:0]; 
        tr.globalAddr[63:32] = 0;
      end
      else
        tr.localAddr[31:24] = internalBus.DATA[7:0];

      // 63:56 WAIT ---------------------------------------
      @(posedge internalBus.CLK);
      randomNotReady(enNotReady); 
      do begin
       @(negedge internalBus.CLK);
      end
      while (internalBus.SRC_RDY_N == 1);

      // 71:64 DATA ---------------------------------------      
      if (tr.transType != L2LW && tr.transType != L2LR) begin
        tr.localAddr[7:0] = internalBus.DATA[7:0];
      end
      else begin         
        tr.globalAddr[ 7 :0]  = internalBus.DATA[7:0];
        tr.globalAddr[63:32]  = 0;
      end

      // 71:64 WAIT ---------------------------------------
      @(posedge internalBus.CLK);
      randomNotReady(enNotReady); 
      do begin
       @(negedge internalBus.CLK);
      end
      while (internalBus.SRC_RDY_N == 1);  

      // 79:72 DATA ---------------------------------------      
      if (tr.transType != L2LW && tr.transType != L2LR) begin
        tr.localAddr[15:8] = internalBus.DATA[7:0];
      end
      else begin         
        tr.globalAddr[15 :8]  = internalBus.DATA[7:0];
        tr.globalAddr[63:32]  = 0;
      end

      // 79:72 WAIT ---------------------------------------
      @(posedge internalBus.CLK);
      randomNotReady(enNotReady); 
      do begin
       @(negedge internalBus.CLK);
      end
      while (internalBus.SRC_RDY_N == 1);        
 
      // 87:80 DATA ---------------------------------------      
      if (tr.transType != L2LW && tr.transType != L2LR) begin
        tr.localAddr[23:16] = internalBus.DATA[7:0];
      end
      else begin         
        tr.globalAddr[23:16]  = internalBus.DATA[7:0];
        tr.globalAddr[63:32]  = 0;
      end

      // 87:80 WAIT ---------------------------------------
      @(posedge internalBus.CLK);
      randomNotReady(enNotReady); 
      do begin
       @(negedge internalBus.CLK);
      end
      while (internalBus.SRC_RDY_N == 1);   

      // 95:88 DATA ---------------------------------------      
      if (tr.transType != L2LW && tr.transType != L2LR) begin
        tr.localAddr[31:24] = internalBus.DATA[7:0];
      end
      else begin         
        tr.globalAddr[31:24]  = internalBus.DATA[7:0];
        tr.globalAddr[63:32]  = 0;
      end

      // 95:88 WAIT ---------------------------------------
      @(posedge internalBus.CLK);
      randomNotReady(enNotReady); 
      do begin
       @(negedge internalBus.CLK);
      end
      while (internalBus.SRC_RDY_N == 1);                

      // 103:96 DATA --------------------------------------
      if (tr.transType != L2LW && tr.transType != L2LR) begin
        tr.globalAddr[39:32] = internalBus.DATA[7:0];  
      end
      else begin         
        tr.globalAddr[63:32]  = 0;
      end

      // 103:96 WAIT --------------------------------------
      @(posedge internalBus.CLK);
      randomNotReady(enNotReady); 
      do begin
       @(negedge internalBus.CLK);
      end
      while (internalBus.SRC_RDY_N == 1);                      

      // 111:104 DATA -------------------------------------
      if (tr.transType != L2LW && tr.transType != L2LR) begin
        tr.globalAddr[47:40] = internalBus.DATA[7:0];  
      end
      else begin         
        tr.globalAddr[63:32]  = 0;
      end     

      // 111:104 WAIT --------------------------------------
      @(posedge internalBus.CLK);
      randomNotReady(enNotReady); 
      do begin
       @(negedge internalBus.CLK);
      end
      while (internalBus.SRC_RDY_N == 1);     

      // 119:112 DATA -------------------------------------
      if (tr.transType != L2LW && tr.transType != L2LR) begin
        tr.globalAddr[55:48] = internalBus.DATA[7:0];  
      end
      else begin         
        tr.globalAddr[63:32]  = 0;
      end      

      // 119:112 WAIT --------------------------------------
      @(posedge internalBus.CLK);
      randomNotReady(enNotReady); 
      do begin
       @(negedge internalBus.CLK);
      end
      while (internalBus.SRC_RDY_N == 1);                            

      // 127:120 DATA -------------------------------------
      if (tr.transType != L2LW && tr.transType != L2LR) begin
        tr.globalAddr[63:56] = internalBus.DATA[7:0];  
      end
      else begin         
        tr.globalAddr[63:32]  = 0;
      end

      // 127:120 WAIT --------------------------------------
      @(posedge internalBus.CLK);
      
      // Process data if available
      if (tr.transType != L2LR && tr.transType != G2LR)
        receiveData(tr, offset);
    endtask : receiveTransaction

    // -- Receive Data --------------------------------------------------------
    // This function receives transaction data
    task receiveData( InternalBusTransaction tr, int offset );
      bit enNotReady = $urandom_range(8);
      // TODO: Add coments, better variable names
      int word64  = tr.length;
      int low_tr  = 0;
      int low_ib  = 0;
      int high_tr = 7;
      int high_ib = 7;
      tr.data = new[tr.length];

      for (int i=1; i <= word64; i++) begin
        randomNotReady(enNotReady); // Generate random not ready
        //$write("bla %t", $time);
        do begin
         @(negedge internalBus.CLK);
        end
        while (internalBus.SRC_RDY_N == 1);

        // last word
        if (i == word64) begin        
          if (internalBus.EOF_N == 1) begin
            $write("Error: Monitor %d receive transaction with wrong length", monitorId);
            tr.display();
            $stop;
          end;
        end
               
        // One 64-bit copying
        tr.data[low_tr++] = internalBus.DATA; 
  
        @(posedge internalBus.CLK);
      end
    endtask : receiveData  
  endclass : InternalBusMonitor

endpackage : ib_monitor_pkg



