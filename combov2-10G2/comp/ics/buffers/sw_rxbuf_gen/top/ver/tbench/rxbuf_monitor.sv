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
 * $Id: rxbuf_monitor.sv 13927 2010-06-03 14:46:50Z xkoran01 $
 *
 * TODO:
 *
 */
 
  typedef struct {
    int new_len;
    int ifc_no;
  }tNewLenInfo;
  
  import math_pkg::*;
  import sv_rxbuf_pkg::*;
  
  // --------------------------------------------------------------------------
  // -- SW RX Buffer Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for creating transaction objects from 
   * Frame Link interface signals. After is transaction received it is sended
   * by callback to processing units (typicaly scoreboard) Unit must be enabled
   * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call.
   */
  class SwRxBufferMonitor #(int pDataWidth=64, int pBlockSize=2, int pFlows=2, int pTotalFlowSize=16384);
    
    // -- Private Class Atributes --
    string  inst;                            // Monitor identification
    bit     enabled;                         // Monitor is enabled
    MonitorCbs cbs[$];                       // Callbacks list
    virtual iSwRxBuffer.monitor #(pDataWidth,pBlockSize,pFlows,pTotalFlowSize) monitor;
    tTransInfoMbx transInfoMbx;              // Store info about header and body length from driver
    tNewLenInfo newLenQue[$];                // Queue to store received NEW_LEN and NEW_LEN_DV
    tTransInfo  transInfoQue[$];             //
    
    int rd_addr[] = new[pFlows];             // Actual read address for each flow
    int rel_len[] = new[pFlows];             // Bytes count received from each flow
    
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
    
    
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   virtual iSwRxBuffer.monitor #(pDataWidth,pBlockSize,pFlows,pTotalFlowSize) monitor,
                   tTransInfoMbx transInfoMbx
                   );
      this.enabled      = 0;           // Monitor is disabled by default   
      this.monitor      = monitor;     // Store pointer interface 
      this.inst         = inst;        // Store driver identifier
      this.transInfoMbx = transInfoMbx;
      
      foreach (this.rd_addr[i]) this.rd_addr[i]=0;
      foreach (this.rel_len[i]) this.rel_len[i]=0;
      
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
      SwRxBufferTransaction transaction[$]; 
      SwRxBufferTransaction trans;
      Transaction tr;
      while (enabled) begin              // Repeat in forewer loop
        assert(randomize());
        // Wait before receiving transaction
        if (enReqDelay) 
          repeat (reqDelay) begin
            @(monitor.monitor_cb);
            monitor.monitor_cb.RX_RELLEN_DV <= 0;
            if (monitor.monitor_cb.RX_NEWLEN_DV) addNewLen();   // Check for RX_NEWLEN_DV setting
          end  
        receiveTransaction(transaction); // Receive Transaction
        #(0); // Necessary for not calling callback before driver
        if (enabled) begin
          while (transaction.size) begin
            trans = new;
            trans = transaction.pop_front;
            $cast(tr, trans);
            // Call transaction preprocesing, if is available
            foreach (cbs[i]) cbs[i].pre_rx(tr, inst);
            // Call transaction postprocesing, if is available
            foreach (cbs[i]) cbs[i].post_rx(tr, inst);
//            trans.display("MONITOR");
          end  
        end        
      end
    endtask : run
    
    // -- Add New Len -------------------------------------------------
    // It adds NEW_LEN to queue when NEW_LEN_DV
    task addNewLen();
      int minBit, maxBit;     // Borders of NEW_LEN belonging to appropriate ifc
      int new_len=0, m=0;
      tNewLenInfo info;
      
      info.new_len = monitor.monitor_cb.RX_NEWLEN;
      info.ifc_no = monitor.monitor_cb.RX_NEWLEN_IFC;
      newLenQue.push_back(info);  // Add info to queue
               
    endtask : addNewLen
    
    // -- Wait for New Len Dv -------------------------------------------------
    // It waits until NEW_LEN_DV and RD_DST_RDY
    task waitForNewLenDv();
      do begin
        if (!monitor.monitor_cb.RX_NEWLEN_DV) begin
          @(monitor.monitor_cb);
          monitor.monitor_cb.RX_RELLEN_DV <= 0;
        end  
        if (!enabled) return;
      end while (!monitor.monitor_cb.RX_NEWLEN_DV);
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

      if (rd_addr[ifcNo] == (pBlockSize<<(log2(pDataWidth/8)))) // Check last address
        rd_addr[ifcNo] = 0;
      addr = 0;
      addr = ifcNo<<log2(pTotalFlowSize);
      addr += rd_addr[ifcNo];
      rd_addr[ifcNo]+=pDataWidth/8;
      monitor.monitor_cb.RD_REQ  <= 1;
      monitor.monitor_cb.RD_ADDR <= addr;
    endtask : setAddress
    
    // -- Receive Data --------------------------------------------------------
    // It receives data to tr object
    task receiveData(output byte unsigned aux[], input int ifcNo, int newLen);
      int byte_no=0;
      
      for(int i=0; i<newLen+pDataWidth/8; i+=pDataWidth/8)
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
          for (int i=0; i<pDataWidth/8; i++) 
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
    endtask : receiveData      
        
    // -- Parse Data ----------------------------------------------------------
    // It parses received data into transactions
    task parseData(output SwRxBufferTransaction transaction[$], 
                   input byte unsigned aux[], int ifcNo, int trCount);
      tTransInfo transInfo;
      SwRxBufferTransaction tr;
      int m=0, tmp;
      
      // Copy info from mailbox to queue for easier manipulation
      while (transInfoMbx.num()!=0) begin
        transInfoMbx.get(transInfo);
        transInfoQue.push_back(transInfo);
      end
      
      for (int i=0; i<trCount; i++)
      begin
        // Get appropriate transation info
        for (int j=0; j<transInfoQue.size; j++) 
        begin
          if (transInfoQue[j].ifcNo == ifcNo) begin
            transInfo = transInfoQue[j];
            transInfoQue.delete(j);
            break;
          end 
        end
        
        // Prepare transaction for data store
        tr             = new();
        tr.ifcNo       = ifcNo;
        tr.packetCount = 2;
        tr.data        = new[tr.packetCount];
        
        // --- Parse header -------------
        tr.data[0]     = new[transInfo.headerLen];
        
        for (int j=0; j<transInfo.headerLen; j++)
          tr.data[0][j] = aux[m++];
          
        // --- Parse body ---------------
        tr.data[1]     = new[transInfo.bodyLen];
        
        for (int j=0; j<transInfo.bodyLen; j++)
          tr.data[1][j] = aux[m++];  
          
        // Align index
        if ((m%(pDataWidth/8)) !=0) begin
          tmp = m/(pDataWidth/8)+1;
          m   = tmp*(pDataWidth/8);
        end  

        transaction.push_back(tr);
      end
      if (m!=aux.size) $write("Incorrect NewLen\n");  
    endtask : parseData  
    
    // -- Receive Transaction -------------------------------------------------
    // It receives SW RX Buffer transaction to tr object
    task receiveTransaction(output SwRxBufferTransaction transaction[$]);
      byte unsigned aux[];
      tNewLenInfo info;
      int ifcNo;
      int trCount = 0;

      if (newLenQue.size==0) waitForNewLenDv(); // Wait for data ready to output

      // Get ifcNo of next burst read      
      ifcNo = newLenQue[0].ifc_no;
      
      for (int i=0; i<newLenQue.size; i++)
      begin
        // Accumulate newLen
        if (newLenQue[i].ifc_no == ifcNo) begin
          info = newLenQue[i];
          newLenQue.delete(i);
          rel_len[info.ifc_no] += info.new_len;
          trCount++;
          i = -1;
        end
      end 
      
      $write("NewLen:%1d\n",rel_len[ifcNo]);
      // Receive burst of data
      receiveData(aux, ifcNo, rel_len[ifcNo]);
      
      // Parse received data into transations
      parseData(transaction, aux, ifcNo, trCount);  
       
      // Release data
      monitor.monitor_cb.RX_RELLEN_DV <= 1;
      monitor.monitor_cb.RX_RELLEN_IFC <= info.ifc_no;
      monitor.monitor_cb.RX_RELLEN    <= rel_len[info.ifc_no];
      rel_len[info.ifc_no] = 0;
      
    endtask : receiveTransaction
    
  endclass : SwRxBufferMonitor    
