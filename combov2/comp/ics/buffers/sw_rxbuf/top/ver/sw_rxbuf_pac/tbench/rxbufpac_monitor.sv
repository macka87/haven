/*
 * rxbuf_monitor.sv: SW RX Buffer Monitor
 * Copyright (C) 2008 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
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
 * $Id: rxbufpac_monitor.sv 8057 2009-04-05 23:04:27Z xsanta06 $
 *
 * TODO:
 *
 */
 
  typedef struct {
    int new_len;
    int ifc_no;
  }tNewLenInfo;
  
  import math_pkg::*;
  
  // --------------------------------------------------------------------------
  // -- SW RX Buffer Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for creating transaction objects from 
   * Frame Link interface signals. After is transaction received it is sended
   * by callback to processing units (typicaly scoreboard) Unit must be enabled
   * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call.
   */
  class SwRxBufPacMonitor #(int pDataWidth=64, int pBlockSize=2, int pFlows=2, int pTotalFlowSize=16384);
    
    // -- Private Class Atributes --
    string  inst;                            // Monitor identification
    bit     enabled;                         // Monitor is enabled
    MonitorCbs cbs[$];                       // Callbacks list
    virtual iSwRxBuffer.monitor #(pDataWidth,pBlockSize,pFlows,pTotalFlowSize) monitor;
    tNewLenInfo newLenQue[$];                // Queue to store received NEW_LEN and NEW_LEN_DV
    
    int rd_addr[] = new[pFlows];             // Actual read address for each flow
    
    // ----
    rand bit enReqDelay;   // Enable/Disable delays between rd_req
      // Enable/Disable delays between rd_req (weights)
      int reqDelayEn_wt             = 0; 
      int reqDelayDisable_wt        = 1;

    rand integer reqDelay; // Delay between rd_req
      // Delay between rd_req limits
      int reqDelayLow          = 50;
      int reqDelayHigh         = 100;
    // ----
    
    // -- Constrains --
    constraint cDelays {
      enReqDelay dist { 1'b1 := reqDelayEn_wt,
                        1'b0 := reqDelayDisable_wt
                      };

      reqDelay inside {
                       [reqDelayLow:reqDelayHigh]
                      };
    }
    
    const int pDataWidthByte = pDataWidth/8;
    
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   virtual iSwRxBuffer.monitor #(pDataWidth,pBlockSize,pFlows,pTotalFlowSize) monitor
                   );
      this.enabled      = 0;           // Monitor is disabled by default   
      this.monitor      = monitor;     // Store pointer interface 
      this.inst         = inst;        // Store driver identifier
      
      foreach (this.rd_addr[i]) this.rd_addr[i]=0;
      
      monitor.monitor_cb.RX_RELLEN    <= 0;
      monitor.monitor_cb.RX_RELLEN_DV <= 0;
      
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
        setNewLenRdy();  // Randomly sets RX_NEWLEN_RDY signal
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
      SwRxBufPacTransaction transaction; 
      Transaction tr;
      
      while (enabled) begin              // Repeat in forewer loop
        assert(randomize());
        transaction = new();
        // Wait before receiving transaction
        if (enReqDelay) 
          repeat (reqDelay) begin
            @(monitor.monitor_cb);
            monitor.monitor_cb.RX_RELLEN_DV <= 0;
            if (monitor.monitor_cb.RX_NEWLEN_DV) addNewLen();   // Check for RX_NEWLEN_DV setting
          end  
        receiveTransaction(transaction); // Receive Transaction
        #(0); // Necessary for not calling callback before driver
        $cast(tr, transaction);
        // Call transaction preprocesing, if is available
        foreach (cbs[i]) cbs[i].pre_rx(tr, inst);
        // Call transaction postprocesing, if is available
        foreach (cbs[i]) cbs[i].post_rx(tr, inst);
//        transaction.display("MONITOR");       
      end
    endtask : run
    
    
    // -- Set New Len Rdy -----------------------------------------------------
    // It randomly sets RX_NEW_LEN_RDY signal
    task setNewLenRdy();
      while (enabled) begin
        monitor.monitor_cb.RX_NEWLEN_RDY <= $urandom_range(pow(2,pFlows)-1,0);
        @(monitor.monitor_cb);
      end
    endtask: setNewLenRdy
    
    
    // -- Add New Len -------------------------------------------------
    // It adds NEW_LEN to queue when NEW_LEN_DV
    task addNewLen();
      int minBit, maxBit;     // Borders of NEW_LEN belonging to appropriate ifc
      int new_len=0, m=0;
      tNewLenInfo info;
      
      for (int i=0; i<pFlows; i++)
      begin
        if (monitor.monitor_cb.RX_NEWLEN_DV[i] && monitor.monitor_cb.RX_NEWLEN_RDY[i])
        begin
          minBit = 16*i;           // Set borders
          maxBit = 16*(i+1);
          for (int j=minBit; j<maxBit; j++)
          begin
            if (monitor.monitor_cb.RX_NEWLEN[j]==1) new_len+=pow(2,m); // Get New Len
            m++;
          end
          info.new_len   = new_len;  
          info.ifc_no    = i;

          newLenQue.push_back(info);  // Add info to queue
          new_len=0;
          m=0;
        end
      end
         
    endtask : addNewLen
    
    // -- Wait for New Len Dv -------------------------------------------------
    // It waits until NEW_LEN_DV and RD_DST_RDY
    task waitForNewLenDv();
      do begin
        if (!(monitor.monitor_cb.RX_NEWLEN_DV & monitor.monitor_cb.RX_NEWLEN_RDY)) begin
          @(monitor.monitor_cb);
          monitor.monitor_cb.RX_RELLEN_DV <= 0;
        end  
        if (!enabled) return;
      end while (!(monitor.monitor_cb.RX_NEWLEN_DV & monitor.monitor_cb.RX_NEWLEN_RDY));
      addNewLen();                                // New Len is set
    endtask : waitForNewLenDv
    
    // -- Wait for DST_RDY ----------------------------------------------------
    // It waits until DST_RDY and ARDY
    task waitForDstRdy(); // Cekej dokud neni DST_RDY A ARDY
      do begin
        @(monitor.monitor_cb);
        monitor.monitor_cb.RX_RELLEN_DV <= 0;
        if (monitor.monitor_cb.RX_NEWLEN_DV) addNewLen();   // Check for RX_NEWLEN_DV setting
      end while (!monitor.monitor_cb.RD_ARDY || !monitor.monitor_cb.RD_DST_RDY); //Detect Destination Ready
    endtask : waitForDstRdy    
    
    // -- Set Address ---------------------------------------------------------
    // It sets address for next read  
    task setAddress(int ifcNo);
      logic [31:0] addr = 0;

      if (rd_addr[ifcNo] == (pBlockSize<<(log2(pDataWidthByte)))) // Check last address
        rd_addr[ifcNo] = 0;
      addr = 0;
      addr = ifcNo<<log2(pTotalFlowSize);
      addr += rd_addr[ifcNo];
      rd_addr[ifcNo]+=pDataWidthByte;
      monitor.monitor_cb.RD_REQ  <= 1;
      monitor.monitor_cb.RD_ADDR <= addr;
    endtask : setAddress
    
    // -- Receive Data --------------------------------------------------------
    // It receives data to tr object
    task receiveData(output SwRxBufPacTransaction transaction, input int ifcNo, int newLen);
      int byte_no=0;
      byte unsigned aux[];
      
      for(int i=0; i<newLen+pDataWidthByte; i+=pDataWidthByte)
      begin
        if (i<newLen) begin
          // Set Address
          setAddress(ifcNo);
          waitForDstRdy();
        end
        else begin
          @(monitor.monitor_cb);
          monitor.monitor_cb.RX_RELLEN_DV <= 0;
          if (monitor.monitor_cb.RX_NEWLEN_DV) addNewLen();   // Check for RX_NEWLEN_DV setting
        end  
        
        // Process one word
        if (i>0) begin
          for (int i=0; i<pDataWidthByte; i++) 
          begin
            logic [7:0] wbyte = 0;
            for (int j=0; j<8; j++)
              wbyte[j] = monitor.monitor_cb.RD_DATA[i*8 + j];   // Process one byte
            aux=new[byte_no+1](aux);    
            aux[byte_no] = wbyte;
            byte_no++;
          end
        end 

        monitor.monitor_cb.RD_REQ  <= 0;
      end
      
      // Store received data into transation
      storeData(transaction, aux, ifcNo, newLen);
      
    endtask : receiveData      
        
    // -- Parse Data ----------------------------------------------------------
    // It parses received data into transactions
    task storeData(output SwRxBufPacTransaction tr, input byte unsigned aux[], 
                   int ifcNo, int newLen);

      // Prepare transaction for data store
      tr             = new();
      tr.ifcNo       = ifcNo;
      tr.packetCount = 1;
      tr.data        = new[tr.packetCount];
      
      // --- Store data ---------------
      tr.data[0]     = new[newLen](aux);
  
    endtask : storeData  
    
    // -- Receive Transaction -------------------------------------------------
    // It receives SW RX Buffer transaction to tr object
    task receiveTransaction(output SwRxBufPacTransaction transaction);
      tNewLenInfo   info;

      if (newLenQue.size==0) waitForNewLenDv(); // Wait for data ready to output

      // Get ifcNo of next burst read      
      info = newLenQue.pop_front();

      // Receive data
      receiveData(transaction, info.ifc_no, info.new_len);  

      // Release data
      monitor.monitor_cb.RX_RELLEN_DV[info.ifc_no] <= 1;
      monitor.monitor_cb.RX_RELLEN    <= info.new_len<<(16*info.ifc_no);
      
    endtask : receiveTransaction
    
  endclass : SwRxBufPacMonitor    
