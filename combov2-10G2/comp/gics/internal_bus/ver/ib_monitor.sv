/*
 * ib_monitor.sv: InternalBus Monitor
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
 * $Id: ib_monitor.sv 11163 2009-09-14 13:47:00Z washek $
 *
 * TODO:
 *
 */
 
 
  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for creating transaction objects from 
   * Internal Bus interface signals. After a transaction is received it is sent
   * by callback to processing units (typicaly scoreboard) Unit must be enabled
   * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call.
   */
  class InternalBusMonitor #(int DATA_WIDTH=64);
    
    // -- Private Class Atributes --
    string  inst;                          // Monitor identification
    bit     enabled;                       // Monitor is enabled
    bit     busy;                          // Monitor is receiving transaction
    MonitorCbs cbs[$];                     // Callbacks list
    virtual iInternalBusTx.tb #(DATA_WIDTH) ib;
    
    parameter int ALIGN_WIDTH = max(log2(DATA_WIDTH/8),1);
    
    // Delays probabilities and limits
    pIbMonitorDelays D;
  
    rand bit enDelay;        // Enable/Disable delays between transactions
    rand int delay;          // Delay between transactions
    rand bit enInsideDelay;  // Enable/Disable delays inside transaction
    rand int insideDelay;    // Delay inside transactions
    
    // -- Constrains --
    constraint cDelays {
      enDelay dist { 1'b1 := D.outEnWt,
                     1'b0 := D.outDisWt };
  
      delay inside { [D.outLow : D.outHigh] };
  
      enInsideDelay dist { 1'b1 := D.inEnWt,
                           1'b0 := D.inDisWt };
      
      insideDelay inside { [D.inLow : D.inHigh] };
    }
    
        
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   virtual iInternalBusTx.tb #(DATA_WIDTH) ib,
                   pIbMonitorDelays delays = dIbMonitorDelays );
      this.enabled   = 0;       // Monitor is disabled by default
      this.busy      = 0;       // Busy bit  
      this.ib        = ib;      // Store pointer interface 
      this.inst      = inst;    // Store driver identifier
      this.D         = delays;

      // Setting default values for Internal Bus interface
      ib.cb.DST_RDY_N <= 1;
      
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
        runDelays(); // Creating subprocess for generating delays
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Monitor -----------------------------------------------------
    // Disable monitor
    task setDisabled();
      enabled = 0; // Disable monitor, after receiving last transaction
    endtask : setDisabled 
    
    // -- Run Monitor ---------------------------------------------------------
    // Receive transactions and send them for processing by call back
    task run();
      InternalBusTransaction transaction; 
      Transaction tr;
      while (enabled) begin              // Repeat in forewer loop
        transaction = new;               // Create new transaction object
        receiveTransaction(transaction); // Receive Transaction
        @(ib.cb);
        if (enabled) begin
          $cast(tr, transaction);
          // Call transaction preprocesing, if is available
          foreach (cbs[i]) cbs[i].pre_rx(tr, inst);
          // Call transaction postprocesing, if is available
          foreach (cbs[i]) cbs[i].post_rx(tr, inst);
        end
      end
    endtask : run
    
    // -- Receive Transaction -------------------------------------------------
    // It receives InternalBus transaction to tr object
    task receiveTransaction(InternalBusTransaction tr);
      int bit_no = 0, h_bit_no = 0; //number of read bytes
      logic [127:0] header;
      logic data[];
      int i;
      int length, offset;
      bit loop = 1;
      
      busy = 0;
      
      //Detect Start of Frame
      while (ib.cb.SOF_N==1 || ib.cb.SRC_RDY_N==1) begin
         @(ib.cb);
         if (!enabled) return;
      end
      
      busy = 1;
      
      while (loop) begin
         //Wait to DST_RDY and SRC_RDY
         while (ib.cb.DST_RDY_N == 1 || ib.cb.SRC_RDY_N == 1)
            @(ib.cb);
         
         //Get data
         if (h_bit_no < 128) //header
            for (i=0; i<DATA_WIDTH; i++)
               header[h_bit_no++] = ib.cb.DATA[i];
         else begin //data
            data = new[bit_no+DATA_WIDTH](data);
            for (i=0; i<DATA_WIDTH; i++)
              data[bit_no++] = ib.cb.DATA[i];
         end
         
         //End if SOF_N
         if (ib.cb.EOF_N == 0)
            loop = 0;
         else
            @(ib.cb);
      end
      
      // --------- Store received data into transaction -------------
      
      tr.transType    = header[3:0];
      tr.length[11:0] = header[15:4];
      tr.tag          = header[23:16];
      tr.localAddr    = header[95:64];
      tr.globalAddr   = {header[127:96],header[63:32]};
      
      tr.length[12] = (header[15:4] == 12'h000) ? 1'b1 : 1'b0;
      
      length = tr.length;
      
      if (tr.haveData()) begin
        if (data.size < length*8 || data.size - length*8 > DATA_WIDTH*2-16)
          $display($time," ",inst,": Length of transaction (",data.size/8,
                   ") doesn't match length specified in header (",length,").");
        
        if (DATA_WIDTH > 8)
          offset = tr.globalAddr[ALIGN_WIDTH-1:0];
        else
          offset = 0;
        
        tr.data = new[length];
        for (int i = 0; i<length; i++)
          for (int j=0; j<8; j++)
            tr.data[i][j] = data[(i+offset)*8+j];
      end

    endtask : receiveTransaction
    
    
    // -- Delays subprocess ---------------------------------------------------
    // 
    task runDelays();
      // randomize waits
      //assert(randomize());
      
      // Repeat while enabled
      while (enabled) begin
        
        //Uncomment to test, if unit sets SRC_RDY_N independently of DST_RDY_N
        //wait (ib.cb.SRC_RDY_N == 0);
        
        ib.cb.DST_RDY_N <= 0;
        assert(randomize());
        
        if (ib.cb.EOF_N == 0 && ib.cb.SRC_RDY_N == 0) begin
          // delay between transactions
          if (enDelay) begin
            repeat (delay) begin
              ib.cb.DST_RDY_N <= 1;
              @(ib.cb);
            end
            ib.cb.DST_RDY_N   <= 0;
            if (delay > 0) @(ib.cb);
          end
        
        end else begin
          // delay inside transaction
          if (enInsideDelay) begin
            repeat (insideDelay) begin
                ib.cb.DST_RDY_N <= 1;
                @(ib.cb);
            end
          end
          ib.cb.DST_RDY_N   <= 0;
        end
        
        // destination ready active for one cycle
        @(ib.cb);
      end

      ib.cb.DST_RDY_N <= 1;
    endtask : runDelays
    
    
  endclass : InternalBusMonitor    
