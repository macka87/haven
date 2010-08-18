//
// ib_monitor.sv: System Verilog Internal Bus Monitor
// Copyright (C) 2008 CESNET
// Author(s): Petr Kobierský <kobierskyk@liberouter.org>
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
// $Id: ib_monitor.sv 3565 2008-07-15 15:02:13Z xkobie00 $
//

  // --------------------------------------------------------------------------
  // -- Internal Bus Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for creating transaction objects from 
   * Internal Bus interface signals. After is transaction received it is sended
   * by callback to processing units (typicaly scoreboard) Unit must be enabled
   * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call.
   */
  class InternalBusMonitor#(int pDataWidth=64);
    
    // -- Private Class Atributes --
    string  inst;                            // Monitor identification
    bit     enabled;                         // Monitor is enabled
    MonitorCbs cbs[$];                       // Callbacks list
    virtual iInternalBusTx.monitor #(pDataWidth) internalBus;

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   virtual iInternalBusTx.monitor #(pDataWidth) internalBus
                 );
      this.inst        = inst;
      this.enabled     = 0;           // Monitor is disabled by default   
      this.internalBus = internalBus; // Store pointer interface 
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
    // -- Run Monitor ---------------------------------------------------------
    // Receive transactions and send them for processing by call back
    task run();
      InternalBusTransaction transaction;  
      Transaction tr;
      while (enabled) begin              // Repeat in forewer loop
        transaction = new;               // Create new transaction object
        receiveTransaction(transaction); // Receive Transaction
        if (enabled) begin                                                           
          $cast(tr, transaction);
          // Call transaction preprocesing, if is available
          foreach (cbs[i]) cbs[i].pre_rx(tr, inst);
          // Call transaction postprocesing, if is available
          foreach (cbs[i]) cbs[i].post_rx(tr, inst);
        end
      end
    endtask : run

    // -- Wait for SOP --------------------------------------------------------
    // It waits until SOP and SRC_RDY
    task waitForSOP(); // Cekej dokud neni SOP A SRC RDY
      do begin
        if (internalBus.cb_monitor.SOP_N || internalBus.cb_monitor.SRC_RDY_N)
          @(internalBus.cb_monitor);
      end while (internalBus.cb_monitor.SOP_N || internalBus.cb_monitor.SRC_RDY_N); //Detect Start of Packet
    endtask : waitForSOP
  
    // -- Wait for DST_RDY ----------------------------------------------------
    // It waits until DST_RDY and SRC_RDY
    task waitForDstRdy(); // Cekej dokud neni DST_RDY A SRC RDY
      do begin
        if (internalBus.cb_monitor.DST_RDY_N || internalBus.cb_monitor.SRC_RDY_N)
          @(internalBus.cb_monitor);
      end while (internalBus.cb_monitor.DST_RDY_N || internalBus.cb_monitor.SRC_RDY_N); //Detect Destination Ready
    endtask : waitForDstRdy
   

    // -- Receive Transaction -------------------------------------------------
    // It receives Internal Bus transaction to tr object
    task receiveTransaction( InternalBusTransaction tr);
      int offset; // Data offset

      //--- Process First HDR -------------------------------------------------
      waitForSOP();     // Wait for active SOP
      waitForDstRdy();  // Wait for src_dst_rdy

      tr.length    = internalBus.cb_monitor.DATA[11: 0]; // Get length
      tr.tag       = internalBus.cb_monitor.DATA[31:16]; // Get tag

      // Get Transaction type
      case (internalBus.cb_monitor.DATA[15:12])
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
        tr.globalAddr[31: 0] = internalBus.cb_monitor.DATA[63:32]; 
        tr.globalAddr[63:32] = 0;
        end
      else
        tr.localAddr = internalBus.cb_monitor.DATA[63:32];

      offset = internalBus.cb_monitor.DATA[34:32]; // Store data offset

      //--- Process Second HDR -----------------------------------------------     
      @(internalBus.cb_monitor); // Wait for clock cycle
      waitForDstRdy();           // Wait for src_dst_rdy

      // Store address from second header
      if (tr.transType != L2LW && tr.transType != L2LR) begin  
        tr.globalAddr[63:32] = internalBus.cb_monitor.DATA[63:32];  
        tr.localAddr = internalBus.cb_monitor.DATA[31:0];
        end
      else begin         
        tr.globalAddr[31 :0]  = internalBus.cb_monitor.DATA[31:0];
        tr.globalAddr[63:32]  = 0;
        end
      
      // Process data if available
      if (tr.transType != L2LR && tr.transType != G2LR)
        receiveData(tr, offset);
      else
        if (internalBus.cb_monitor.EOP_N == 1) begin
            $write("Error: IB Monitor %s receive transaction without EOP: ", inst);
            tr.display();
            $stop;
            end
    endtask : receiveTransaction

    // -- Receive Data --------------------------------------------------------
    // This function receives transaction data
    task receiveData( InternalBusTransaction tr, int offset );
      // TODO: Add coments, better variable names
      int lenaux  = (tr.length == 0) ? 4096 : tr.length;
      int word64  = (lenaux + offset + 7)/8;
      int low_tr  = 0;
      int low_ib  = 0;
      int high_tr = 7;
      int high_ib = 7;
      tr.data = new[lenaux];

      for (int i=1; i <= word64; i++) begin
        @(internalBus.cb_monitor);
        waitForDstRdy();
        
        // first word
        if (i == 1) 
          low_ib = offset;              
        else
          low_ib = 0;
          
        // last word
        if (i == word64) begin        
          high_tr -= (8 - ((lenaux) % 8));
          high_ib  = ( ((lenaux + offset) - 1) % 8); 
          if (internalBus.cb_monitor.EOP_N == 1) begin
            $write("Error: IB Monitor %s receive transaction with wrong length: ", inst);
            tr.display();
            $stop;
          end;
        end
               
        // One 64-bit copying
        for (low_ib = low_ib; low_ib <= high_ib ; low_ib++) begin 
          logic [7:0] wbyte = 0;
          for (int j=0; j<8; j++)
            wbyte[j] = internalBus.cb_monitor.DATA[low_ib*8 + j]; 
          tr.data[low_tr++] = wbyte;
        end          
  
        high_tr += 8;     
      end

    endtask : receiveData  
  endclass : InternalBusMonitor

