/*
 * \file ram_monitor.sv
 * \brief Monitor for software memory
 * \author Marek Santa <xsanta06@stud.fit.vutbr.cz>
 * \date 2009 
 */
 /*
 * Copyright (C) 2009 CESNET
 * 
 * LICENSE TERMS 
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
 * $Id: ram_monitor.sv 14168 2010-06-24 11:04:08Z xsanta06 $
 *
 * TODO:
 *
 */
 
  import sv_dmamodule_pkg::*;
   
  // --------------------------------------------------------------------------
  // -- RAM Monitor Class
  // --------------------------------------------------------------------------
  
  /*!
   * \brief RAM Monitor Class
   * 
   * This class is responsible for getting transactions from software buffer in 
   * RAM memory. After transaction is received it is sended by callback to 
   * scoreboard. Unit must be enabled by "setEnable()" function call. 
   * Monitoring can be stoped by "setDisable()" function call.  
   * 
   * \param pDataWidth - data width
   * \param pFLows - count of flows
   * \param pPageSize - size of one page
   * \param pPageCount - count of size in one flow                
   */ 
  class RamMonitor #(int pDataWidth = 64, int pFlows = 2, int pPageSize = 4096, int pPageCount = 2);
    
    // -- Private Class Atributes --
    
    //! Modul identification
    string       inst;                         
    //! Modul is enabled
    bit          enabled;  
    //! Callbacks list                    
    MonitorCbs   cbs[$];    
    //! Software memory                   
    DmaModuleSW #(pDataWidth, pFlows, pPageSize, pPageCount)  ram;         
    //! Upstream handler
    IbUpstream #(pDataWidth, pFlows, pPageSize, pPageCount)   ibUpstream;  
    //! Downstream handler
    IbDownstream #(pDataWidth, pFlows, pPageSize, pPageCount) ibDownstream;
    
    //! Start pointers for each flow
    int unsigned startPtr[] = new [pFlows]; 
    //! End pointers for each flows 
    int unsigned endPtr[]   = new [pFlows]; 
    
    // Data width in Bytes
    const int pDataWidthByte = pDataWidth/8;
    // Buffer size
    const int pBufferSize    = pPageSize*pPageCount;
    
    // Controllers status
    logic [pFlows-1:0] rxCtrlStatus = 0; 
    semaphore sem;
    // Pointer zeroized flag
    logic [pFlows-1:0] ptrsZeroized = 0;
    
    // ----
    //! Controllers pause enabling
    bit rxPauseAllowed              = 0;
    //! Pausing all TX controllers at the same time
    bit rxPauseAll                  = 0;
    
    // ----
    rand int pauseDelay;   // Enable/Disable delays between transactions
      // Enable/Disable delays between transaction (weights)
      int pauseDelayLow             = 20000; 
      int pauseDelayHigh            = 25000;

    rand int insidePauseDelay; // Delay between transactions
      // Delay between transactions limits
      int insidePauseDelayLow       = 5000;
      int insidePauseDelayHigh      = 10000;

    // ----
    //! Controllers stop enabling
    bit rxStopAllowed              = 0;
    //! Stopping all TX controllers at the same time
    bit rxStopAll                  = 0;
    
    // ----
    rand int stopDelay;   // Enable/Disable delays between transactions
      // Enable/Disable delays between transaction (weights)
      int stopDelayLow             = 20000; 
      int stopDelayHigh            = 25000;

    rand int insideStopDelay; // Delay between transactions
      // Delay between transactions limits
      int insideStopDelayLow       = 5000;
      int insideStopDelayHigh      = 10000;
    // ----
    
    // -- Constrains --
    constraint cDelays {
      pauseDelay inside {
                         [pauseDelayLow:pauseDelayHigh]
                        };

      insidePauseDelay inside {
                         [insidePauseDelayLow:insidePauseDelayHigh]
                        };               
      
      stopDelay inside {
                         [stopDelayLow:stopDelayHigh]
                        };

      insideStopDelay inside {
                         [insideStopDelayLow:insideStopDelayHigh]
                        };            
      }
    
    // -- Public Class Methods --

    // ------------------------------------------------------------------------
    //! Constructor 
    /*!
     * Creates modul object and sets default values of InternalBus interface signals 
     */
    function new ( string inst, 
                   DmaModuleSW #(pDataWidth, pFlows, pPageSize, pPageCount)  ram,
                   IbUpstream #(pDataWidth, pFlows, pPageSize, pPageCount)   ibUpstream,
                   IbDownstream #(pDataWidth, pFlows, pPageSize, pPageCount) ibDownstream
                   );
                               
      this.enabled      = 0;            // Driver is disabled by default
      this.inst         = inst;         // Store driver identifier
      this.ram          = ram;
      this.ibUpstream   = ibUpstream;
      this.ibDownstream = ibDownstream;
      this.sem          = new(1);
      
      // Initiate pointers
      for (int i=0; i<pFlows;i++) begin
        startPtr[i] = 0;
        endPtr[i]   = 0;
      end  
    endfunction: new          
    
    // ------------------------------------------------------------------------
    //! Set Callbacks 
    /*
     * Put callback object into List 
     * \param cbs - monitor callbacks     
     */      
    function void setCallbacks(MonitorCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks
    
    // ------------------------------------------------------------------------
    //! Enable Monitor 
    /*!
     * Enable Monitor and runs Monitor process
     */ 
    task setEnabled();
      enabled = 1; // Monitor Enabling
      fork         
        run();     // Creating monitor subprocess
        pauseControllers();   // Creating subprocess for pausing controllers
        stopControllers();    // Creating subprocess for stopping controllers
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // ------------------------------------------------------------------------
    //! Disable Monitor 
    /*
     * Disable monitor
     */      
    task setDisabled();
      enabled = 0; // Disable monitor, after receiving last transaction
    endtask : setDisabled
    
    // ------------------------------------------------------------------------
    //! Run Monitor 
    /*
     * Get transactions from RAM and send it to scoreboard
     */
    task run();
      FrameLinkTransaction transaction;
      Transaction to;
      int ifcNo = 0;                   // Number of input FL interface
      string label;                    // Label of appropriate transaction table

      while (enabled) begin                   // Repeat while enabled        
        transaction = new;                    // Create new transaction object
        getTransaction(transaction, ifcNo);   // Receive transaction
        $swrite(label, "Monitor%0d", ifcNo);
        #(0);               // Necessary for not calling callback before driver
        if (enabled) begin
          $cast(to, transaction);
          // Call transaction preprocesing, if is available
          foreach (cbs[i]) cbs[i].pre_rx(to, label);
          // Call transaction postprocesing, if is available
          foreach (cbs[i]) cbs[i].post_rx(to, label);
        end  
//        transaction.display(label);
      end
    endtask : run
    
    // ------------------------------------------------------------------------
    //! Get Transaction 
    /*
     * Gets transaction from RAM
     * \param flTransaction - FrameLink transaction    
     * \param ifcNo - interface number     
     */      
    task getTransaction(FrameLinkTransaction flTransaction, inout int ifcNo);
      // Check emptiness of SW Buffer
      sem.get(1); // lock
      while (endPtr[ifcNo]==startPtr[ifcNo]) begin 
        sem.put(1);  // unlock
        sem.get(1);  // lock
        
        // Go to next ifc
        ifcNo++;
        if (ifcNo == pFlows) ifcNo = 0;
        if (endPtr[ifcNo]!=startPtr[ifcNo]) break;

        ibDownstream.sendEndPtrReq(ifcNo);    // Send Get End Pointer request
        ibUpstream.receiveEndPtr(ifcNo, endPtr[ifcNo]);      // Wait for End Pointer answer
      
        // Pointers were zeroized
        if (ptrsZeroized[ifcNo]==1) begin
          endPtr[ifcNo] = 0;
          ptrsZeroized[ifcNo] = 0;
        end  

      end
      sem.put(1);  // unlock
      
      getFromRAM(flTransaction, ifcNo);
    endtask : getTransaction
    
    // ------------------------------------------------------------------------
    //! Get From RAM 
    /*
     * Gets transaction from the RAM
     * \param flTransaction - FrameLink transaction    
     * \param ifcNo - interface number      
     */      
    task getFromRAM(FrameLinkTransaction tr, int ifcNo);
      byte data[] = new[pDataWidthByte];
      logic [31:0] headerSize = 0;
      logic [31:0] payloadSize = 0;
      int tmp;

      // Copy data
      ram.receiveBufferData(ifcNo,startPtr[ifcNo],data);
      
      //Get header and payload size form first bytes of received data
      for (int j=0; j<=1; j++)
        for (int k=0; k<8; k++) begin
          headerSize[j*8+k] = data[j][k];
          payloadSize[j*8+k] = data[j+2][k];
        end  
          
      // Prepare transaction for data store
      tr.packetCount = 2;
      tr.data        = new[tr.packetCount];
      tr.data[0]     = new[headerSize];
      tr.data[1]     = new[payloadSize];
      
      // ----- Store header data -----
      for(int i=0; i<tr.data[0].size; i+=pDataWidthByte)
      begin
        for (int j=0; j<pDataWidthByte; j++)
          if (i+j<tr.data[0].size) tr.data[0][i+j] = data[j]; 
          
        // Increment start pointer
        startPtr[ifcNo]+=pDataWidthByte;                
        if (startPtr[ifcNo]==pBufferSize) 
          startPtr[ifcNo]=0;
          
        // Get next data word 
        ram.receiveBufferData(ifcNo,startPtr[ifcNo],data);   
      end
      
      // Align header size
      if ((headerSize%(pDataWidth/8)) !=0) begin
        tmp = headerSize/(pDataWidth/8)+1;
        headerSize   = tmp*(pDataWidth/8);
      end 
      
      // Header and payload data in the same word
      if ((headerSize=headerSize%pDataWidthByte) != 0) begin
        // Decrement start pointer
        if (startPtr[ifcNo]==0) 
          startPtr[ifcNo]=pBufferSize;
        startPtr[ifcNo]-=pDataWidthByte;                
        // Get next data word 
        ram.receiveBufferData(ifcNo,startPtr[ifcNo],data);
        
        for (int j=headerSize; j<pDataWidthByte; j++)
          if (j<tr.data[1].size) begin
            tr.data[1][j-headerSize] = data[j];
          end  
          
        // Increment start pointer
        startPtr[ifcNo]+=pDataWidthByte;                
        if (startPtr[ifcNo]==pBufferSize) 
          startPtr[ifcNo]=0;
          
        // Get next data word 
        ram.receiveBufferData(ifcNo,startPtr[ifcNo],data); 
        
        headerSize = pDataWidthByte-headerSize;
      end 
      
      // ---- Store payload data -------
      for(int i=headerSize; i<tr.data[1].size; i+=pDataWidthByte)
      begin
        for (int j=0; j<pDataWidthByte; j++)
          if (i+j<tr.data[1].size) tr.data[1][i+j] = data[j]; 
          
        // Increment start pointer
        startPtr[ifcNo]+=pDataWidthByte;                
        if (startPtr[ifcNo]==pBufferSize) 
          startPtr[ifcNo]=0;
          
        // Get next data word 
        ram.receiveBufferData(ifcNo,startPtr[ifcNo],data);   
      end
     
      // Set new start pointer            
      ibDownstream.setRxStartPtr(startPtr[ifcNo], ifcNo); 
 
    endtask : getFromRAM
    
    // -- Pause Controllers ---------------------------------------------------
    //! Pause controllers
    /*!
     * Pause all RX controllers at the same time or pause controllers randomly.
     */
    task pauseControllers();
      while (enabled && rxPauseAllowed) begin
        int ifcNo;
        
        assert(randomize());           // Randomize rand variables

        // Wait between pausing
        repeat (pauseDelay) @(ibDownstream.ib_down.ib_down_cb);
        
        // -- Pause all RX controllers --
        if (rxPauseAll) begin
          // Pause controllers
          for (int i=0; i<pFlows; i++) begin
            if (rxCtrlStatus[i]==0) begin
              fork
                automatic int j = i;  // Necessary for passing right parameter
                pauseController(j);
              join_none;
            end  
          end    
        end
        // -- Pause random RX controller --
        else begin
          ifcNo = $urandom_range(pFlows-1);
          if (rxCtrlStatus[ifcNo]==0) begin
            fork
              automatic int j = ifcNo; // Necessary for passing right parameter
              pauseController(j);
            join_none;
          end  
        end
      end  
    endtask : pauseControllers
    
    // -- Pause Controller ----------------------------------------------------
    //! Pause controller
    /*!
     * Pause single controller
     * \param ctrlNo - controller number     
     */
    task pauseController(int ifcNo); 
      // Mark controller as paused
      rxCtrlStatus[ifcNo]=1;
      
      // Pause RX controller
      ibDownstream.pauseRxController(ifcNo);  
      
      // Pause time
      repeat (insidePauseDelay) @(ibDownstream.ib_down.ib_down_cb);

      // Unpause RX controller
      ibDownstream.unpauseRxController(ifcNo);  
      // Mark controller as unpaused
      rxCtrlStatus[ifcNo] = 0;
    
    endtask : pauseController 
    
    // -- Stop Controllers ----------------------------------------------------
    //! Stop controllers
    /*!
     * Stop all RX controllers at the same time or stop controllers randomly.
     */
    task stopControllers();
      while (enabled && rxStopAllowed) begin
        int ifcNo;
        
        assert(randomize());           // Randomize rand variables

        // Wait between pausing
        repeat (stopDelay) @(ibDownstream.ib_down.ib_down_cb);

        // -- Stop all RX controllers --
        if (rxStopAll) begin
          // Stop controllers
          for (int i=0; i<pFlows; i++) begin
            if (rxCtrlStatus[i]==0) begin              
              fork
                automatic int j = i;   // Necessary for passing right parameter
                stopController(j);
              join_none;
            end  
          end    
        end
        // -- Stop random RX controller --
        else begin
          ifcNo = $urandom_range(pFlows-1);
          if (rxCtrlStatus[ifcNo]==0) begin
            fork
              automatic int j = ifcNo; // Necessary for passing right parameter
              stopController(j);
            join_none;
          end  
        end
      end  
    endtask : stopControllers
    
    // -- Stop Controller ----------------------------------------------------
    //! Stop controller
    /*!
     * Stop single controller
     * \param ctrlNo - controller number     
     */
    task stopController(int ifcNo); 
      // Mark controller as stopped
      rxCtrlStatus[ifcNo]=1;

      // Stop TX controller
      ibDownstream.stopRxController(ifcNo);  
      
      // Pause time
      repeat (insideStopDelay) @(ibDownstream.ib_down.ib_down_cb);

      // Lock
      sem.get(1);
      // Set both start and end pointer to zero
      endPtr[ifcNo] = 0;
      ibDownstream.setRxEndPtr(endPtr[ifcNo], ifcNo);
      startPtr[ifcNo] = 0;
      ibDownstream.setRxStartPtr(startPtr[ifcNo], ifcNo);
      // Pointers set to zero flag
      ptrsZeroized[ifcNo] = 1;
      // Unlock
      sem.put(1);

      // Unstop RX controller
      ibDownstream.unstopRxController(ifcNo);  
      // Mark controller as unstopped
      rxCtrlStatus[ifcNo] = 0;
    
    endtask : stopController 
    
    // ------------------------------------------------------------------------
    // -- Display functions -----------
    
    //! IB Display 
    /*
     * Displays IB transaction
     */      
    local function void ibDisplay(byte ibTransaction[][]);
      $write ("-----------------------------------\n");
      $write ("-- IB Transaction\n");
      $write ("-----------------------------------\n");
      
      for (int i=0; i<ibTransaction.size; i++)
      begin
        for (int j=0; j<ibTransaction[i].size; j++)
          $write ("%x",ibTransaction[i][j]);
        $write("\n");
      end       
    endfunction : ibDisplay  

endclass : RamMonitor
