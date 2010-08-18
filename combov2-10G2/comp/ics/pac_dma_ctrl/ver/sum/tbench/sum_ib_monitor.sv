/*
 * sum_ib_monitor.sv: InternalBus Monitor for Status Update Manager
 * Copyright (C) 2009 CESNET
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
 * $$
 *
 * TODO:
 *
 */
 
  typedef struct {
    int flow;
    longint globalAddr;
  } tReadRequest;

  // --------------------------------------------------------------------------
  // -- InternalBus Modul Class
  // --------------------------------------------------------------------------
  /* This class is responsible for manipulating with transaction objects from 
   * InternalBus interface signals. Unit must be enabled by "setEnable()" 
   * function call. Monitoring can be stoped by "setDisable()" function call.
   */
  class SumIbMonitor #(int pDataWidth = 64, int pDmaDataWidth = 16, 
                       int pFlows = 2, longint pTxGAddr = 0,
                       int pDmaTag = 0, int pTransType = 0);
    
    // ----------------------
    // -- Class Attributes --
    // ----------------------
    string  inst;                          // Modul identification
    bit     enabled;                       // Modul is enabled
    bit     busy;                          // Monitor is receiving transaction
    mailbox #(tDmaRequest) dmaMbx;         // Parsed DMA request mailbox  
    tReadRequest readReqQue[$];      // Queue for flow number and global address
    int swRxCounter[pFlows];               // Received updates counter
    tTransMbx transMbx;                    // MI32 transaction mailbox
    MonitorCbs cbs[$];                     // Callbacks list
    CheckerMonitorCbs #(pFlows) checkerCbs[$];       // Callbacks list
          
    DmaModul #(pDmaDataWidth, pDmaTag, pTransType) dma;   // DMA ifc monitor
        
    virtual iInternalBus.ib_read_tb #(pDataWidth) ib;

    // ----
    rand bit sendSwRxEn;   // Enable/Disable SW RX counter sending
      // Enable/Disable SW RX counter sending (weights)
      int sendSwRxEn_wt             = 1; 
      int sendSwRxDis_wt            = 5;

    // -- Constrains --
    constraint cDelays {
      sendSwRxEn dist { 1'b1 := sendSwRxEn_wt,
                        1'b0 := sendSwRxDis_wt
                      };
    }


    const int pDataWidthByte = pDataWidth/8;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create driver object 
    function new ( string inst, 
                   tTransMbx transMbx, 
                   DmaModul #(pDmaDataWidth, pDmaTag, pTransType) dma,
                   virtual iInternalBus.ib_read_tb #(pDataWidth) ib
                  );
      this.enabled     = 0;            // Modul is disabled by default
      this.inst        = inst;         // Store modul identifier
      this.transMbx    = transMbx;     // Store pointer to mailbox
      this.dma         = dma;          // DMA modul 
      this.ib          = ib;           // IB modul 
      this.dmaMbx      = dma.dmaMbx;   // Store pointer to mailbox
            
      this.ib.ib_read_cb.RD_ADDR     <= 0;
      this.ib.ib_read_cb.RD_BE       <= '1;
      this.ib.ib_read_cb.RD_REQ      <= 0;
      this.ib.ib_read_cb.RD_DST_RDY  <= 1;

      foreach(swRxCounter[i])
        swRxCounter[i] = 0;
      
    endfunction: new          
    
    // -- Set Callbacks -------------------------------------------------------
    // Put callback object into List 
    function void setCallbacks(MonitorCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks

    // -- Set Checker Callbacks -----------------------------------------------
    // Put callback object into List 
    function void setCheckerCallbacks(CheckerMonitorCbs #(pFlows)cbs);
      this.checkerCbs.push_back(cbs);
    endfunction : setCheckerCallbacks

    // -- Enable Monitor ------------------------------------------------------ 
    // Enable Monitor and runs Monitor process
    task setEnabled();
      enabled = 1;              // Monitor enabling
      fork         
        run();                  // Creating monitor subprocess
        receiveTransaction();
      join_none;                // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Monitor -----------------------------------------------------
    task setDisabled();
      enabled = 0;              // Disable Monitor
    endtask : setDisabled

    // -- Read Request ----------------------------------------------------
    // Set address and request for reading
    task readRequest(logic[31:0] localAddr);
      
      ib.ib_read_cb.RD_ADDR <= localAddr;
      ib.ib_read_cb.RD_BE  <= '1;
      ib.ib_read_cb.RD_REQ  <= 1;
      @(ib.ib_read_cb);

      // Wait for ARDY
      waitForArdy();

      ib.ib_read_cb.RD_REQ  <= 0;
    endtask : readRequest
 
    // -- Run Modul ----------------------------------------------------------
    // Gets DMA request from mailbox and transaction from IB interface
    task run();
      tDmaRequest parsedDma;
      
      while (enabled) begin              // Repeat while enabled

        // Wait if Mailbox is empty
        while (dmaMbx.num()==0) @(ib.ib_read_cb); 
        
        // Monitor receives transaction
        busy = 1;

        // Get request from Mailbox
        dmaMbx.get(parsedDma);                     

        // Set request for reading
        setReadRequest(parsedDma);
      
        // Wait for SRC_RDY
        waitForSrcRdy();

        // Send DMA_DONE
        dma.sendDmaDone(parsedDma.tag);

        // Monitor received transaction and is not busy
        busy = 0;
      end
    endtask : run

    // -- Set Read Request ----------------------------------------------------
    // Set address and request for reading
    task setReadRequest(tDmaRequest parsedDma);
      tReadRequest readReq;

      for (int i=0; i<parsedDma.length/pDataWidthByte; i++)
      begin
        ib.ib_read_cb.RD_ADDR <= parsedDma.localAddr;
        ib.ib_read_cb.RD_BE  <= '1;
        ib.ib_read_cb.RD_REQ  <= 1;
        @(ib.ib_read_cb);

        // Push info about read request into queue
        readReq.flow       = parsedDma.localAddr/'h1000;
        readReq.globalAddr = parsedDma.globalAddr;
        readReqQue.push_back(readReq);

        // Wait for ARDY
        waitForArdy();

        // Process to next address
        parsedDma.localAddr  += pDataWidthByte;
        parsedDma.globalAddr += pDataWidthByte;
        ib.ib_read_cb.RD_REQ  <= 0;
      end  
    endtask : setReadRequest
    
    // -- Receive Transaction -------------------------------------------------
    // Receive transaction and parse data
    task receiveTransaction();
      tReadRequest readReq;
      bit[63:0] globalAddr;
      
      while (enabled) begin
        assert(randomize());

        // Wait for next global address
        while(readReqQue.size == 0)
          @(ib.ib_read_cb);

        // Get data
        globalAddr = readReqQue[0].globalAddr;

        // TX Update
        if(globalAddr == pTxGAddr) 
          processTxUpdate();
        // RX Update
        else 
          processRxUpdate();

      end  
    endtask : receiveTransaction

    // -- Process TX Update ---------------------------------------------------
    // Set address and request for reading
    task processTxUpdate();
      tReadRequest readReq;
      logic [pDataWidth-1:0] data;

      // We get two counter values in one word
      for (int i=0; i<pFlows/2; i++) begin
        // Wait for SRC_RDY
        waitForSrcRdy();
        readReq = readReqQue.pop_front();

        data = ib.ib_read_cb.RD_DATA;

        // Necessary for not calling callback after monitor disabling
        if (!enabled) break;

        #(0); // Necessary for not calling callback before driver
        
        // Call transaction postprocesing, if is available
        foreach (checkerCbs[j]) checkerCbs[j].post_rx(data[31:0], 2*i);
        foreach (checkerCbs[j]) checkerCbs[j].post_rx(data[63:32], 2*i+1);

        @(ib.ib_read_cb);
      end

      // If flow count is odd, receive counter value for last flow
      if(pFlows%2 == 1) begin
        // Wait for SRC_RDY
        waitForSrcRdy();
        readReq = readReqQue.pop_front();

        data = ib.ib_read_cb.RD_DATA;

        #(0); // Necessary for not calling callback before driver
        
        // Call transaction postprocesing, if is available
        foreach (checkerCbs[j]) checkerCbs[j].post_rx(data[31:0], pFlows-1);

        @(ib.ib_read_cb);
      end

    endtask : processTxUpdate

    // -- Process RX Update ---------------------------------------------------
    // Set address and request for reading
    task processRxUpdate();
      SumTransaction transaction;
      Transaction tr;
      tReadRequest readReq;
      logic [pDataWidth-1:0] data;

      transaction = new();
      $cast(tr, transaction);

      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_rx(tr, inst);       

      // Wait for SRC_RDY
      waitForSrcRdy();
      readReq = readReqQue.pop_front();

      data = ib.ib_read_cb.RD_DATA;
      // Parse data and create transaction
      createTransaction(data, transaction, readReq.globalAddr);
      // Update respective SW RX counter
      swRxCounter[readReq.flow/2]++;
      @(ib.ib_read_cb);

      // Wait for SRC_RDY
      waitForSrcRdy();
      readReq = readReqQue.pop_front();
      @(ib.ib_read_cb);

      // Send SW RX counter
      if (sendSwRxEn) begin
        fork // Necessary for avoid blocking by mailbox
          sendSwRxCounter(readReq.flow);
        join_none;
      end  

      #(0); // Necessary for not calling callback before driver
      
      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_rx(tr, inst);
    endtask : processRxUpdate

    // -- Create Transaction --------------------------------------------------
    // Parse receiver data and make SUM transaction
    task createTransaction(logic[pDataWidth-1:0] data, 
                           inout SumTransaction tr, input longint globalAddr); 

      tr.descAddr = globalAddr;
      tr.intFlag  = data[32];
      tr.lfFlag   = data[33];
      tr.length   = data[31:0];

    endtask : createTransaction
   
    // -- Send SW RX Counter --------------------------------------------------
    task sendSwRxCounter(int flow); 
      Mi32Transaction tr = new();

      // Set transaction variables
      tr.address = {flow,6'h14};
      tr.data    = swRxCounter[flow/2];
      tr.be      = '1;
      tr.rw      = 1;

      // Put transaction to mailbox
      transMbx.put(tr);
//      $write("SwRxCounter[%0d]:%0d\n",flow/2,swRxCounter[flow/2]);
    endtask : sendSwRxCounter
   
    // -- Wait for RD_SRC_RDY -------------------------------------------------
    task waitForSrcRdy(); 
      while (ib.ib_read_cb.RD_SRC_RDY==0)
        @(ib.ib_read_cb);
    endtask : waitForSrcRdy
   
    // -- Wait for RD_ARDY ----------------------------------------------------
    task waitForArdy(); 
      while (ib.ib_read_cb.RD_ARDY==0)
        @(ib.ib_read_cb);
    endtask : waitForArdy
   
  endclass : SumIbMonitor 
