/*
 * \file ram_driver.sv
 * \brief Driver for software memory
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
 * $Id: ram_driver.sv 8686 2009-06-05 18:32:33Z xsanta06 $
 *
 * TODO:
 *
 */
 
  import sv_dmamodule_pkg::*;
   
  // --------------------------------------------------------------------------
  // -- RAM Driver Class
  // --------------------------------------------------------------------------
  
  /*!
   * \brief RAM Driver Class
   * 
   * This class is responsible for storing transactions in software buffer in 
   * RAM memory. Transactions are received by 'transMbx'(Mailbox) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call.
   *    
   * \param pDataWidth - data width
   * \param pFLows - count of flows
   * \param pPageSize - size of one page
   * \param pPageCount - count of size in one flow                
   */ 
  class RamDriver #(int pDataWidth = 64, int pFlows = 2, int pPageSize = 4096, int pPageCount = 2);
    
    // -- Private Class Atributes --
    
    //! Driver identification
    string       inst;    
    //! Driver is enabled                     
    bit          enabled;  
    //! Transaction mailbox                   
    tTransMbx    transMbx; 
    //! Callbacks list                    
    DriverCbs    cbs[$];   
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
    logic [pFlows-1:0] txCtrlStatus = 0; 
    // Processing packet for corresponding interface
    logic [pFlows-1:0] inProcessing = 0;
    
    // ----
    //! Controllers pause enabling
    bit txPauseAllowed              = 0;
    //! Pausing all TX controllers at the same time
    bit txPauseAll                  = 0;
    
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
    bit txStopAllowed              = 0;
    //! Stopping all TX controllers at the same time
    bit txStopAll                  = 0;
    
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
                   tTransMbx transMbx,
                   DmaModuleSW #(pDataWidth, pFlows, pPageSize, pPageCount)  ram,
                   IbUpstream #(pDataWidth, pFlows, pPageSize, pPageCount)   ibUpstream,
                   IbDownstream #(pDataWidth, pFlows, pPageSize, pPageCount) ibDownstream
                   );
                               
      this.enabled      = 0;            // Driver is disabled by default
      this.transMbx     = transMbx;     // Store pointer to mailbox
      this.inst         = inst;         // Store driver identifier
      this.ram          = ram;
      this.ibUpstream   = ibUpstream;
      this.ibDownstream = ibDownstream;
      
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
     * \param cbs - driver callbacks     
     */ 
    function void setCallbacks(DriverCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks
    
    // ------------------------------------------------------------------------
    //! Enable Driver 
    /*!
     * Enable Driver and runs Driver process
     */ 
    task setEnabled();
      enabled = 1; // Driver Enabling
      fork         
        run();                // Creating driver subprocess
        pauseControllers();   // Creating subprocess for pausing controllers
        stopControllers();    // Creating subprocess for stopping controllers
      join_none;   // Don't wait for ending

    endtask : setEnabled
        
    // ------------------------------------------------------------------------
    //! Disable Driver 
    /*
     * Disable Driver
     */ 
    task setDisabled();
      enabled = 0; // Disable driver, after sending last transaction it ends
    endtask : setDisabled
    
    // ------------------------------------------------------------------------
    //! Run Driver
    /*
     * Take transactions from mailbox and put them into RAM
     */      
    task run();
      FrameLinkTransaction transaction;
      Transaction to;
      int ifcNo;                       // Number of output FL interface
      string label;                    // Label of appropriate transaction table

      while (enabled) begin            // Repeat while enabled        
        transMbx.get(to);              // Get transaction from mailbox
        $cast(transaction,to);

        // Get interface number
        ifcNo = $urandom_range(pFlows-1);
        while (txCtrlStatus[ifcNo]==1) begin
          @(ibDownstream.ib_down.ib_down_cb);
          ifcNo = $urandom_range(pFlows-1);
        end
        
        // Processing packet for corresponding interface
        inProcessing[ifcNo] = 1;
        
        $swrite(label, "Driver%0d", ifcNo);
        // Call transaction preprocesing, if is available
        foreach (cbs[i]) cbs[i].pre_tx(to, label);
        putTransaction(transaction, ifcNo);   // Send Transaction
//        transaction.display(label);
        // Call transaction postprocesing, if is available
        foreach (cbs[i]) cbs[i].post_tx(to, label);
        
        // End processing packet for corresponding interface
        inProcessing[ifcNo] = 0;
      end
    endtask : run
    
    // ------------------------------------------------------------------------
    //! Put Transaction 
    /*
     * Puts transaction into RAM
     * \param flTransaction - FrameLink transaction
     * \param ifcNo - interface number            
     */      
    task putTransaction(FrameLinkTransaction flTransaction, int ifcNo);
      byte ibTransaction[][];

      flTransactionToIbTransaction(flTransaction, ibTransaction);

      putIntoRAM(ibTransaction, ifcNo);
    endtask : putTransaction
    
    // ------------------------------------------------------------------------
    //! FL Transaction to IB Transaction 
    /*
     * Makes IB transaction from FL transaction
     * \param flTransaction - FrameLink transaction
     * \param ibTransaction - InternalBus transaction          
     */      
    function void flTransactionToIbTransaction(FrameLinkTransaction flTransaction,
                                               output byte ibTransaction[][]);
      int headerSize  = flTransaction.data[0].size;  // Header data size
      int headerSizeRounded = headerSize+4;
      int payloadSize = flTransaction.data[1].size;  // Payload data size
      int payloadSizeRounded = payloadSize;
      logic [15:0] ibSize, ibHeaderSize;
      int wordNo, byteNo;                            // Offset in ibTransaction
            
      // Get rounded header size
      if ((headerSize+4)%pDataWidthByte!=0) 
        headerSizeRounded = ((headerSize+4)/pDataWidthByte+1)*pDataWidthByte;
      
      // Get rounded payload size
      if (payloadSize%(pDataWidth/8)!=0) 
        payloadSizeRounded = (payloadSize/pDataWidthByte+1)*pDataWidthByte;
      
      // Allocate space for new IB transaction
      ibTransaction = new[(headerSizeRounded+payloadSizeRounded)/pDataWidthByte];
      foreach(ibTransaction[i]) ibTransaction[i] = new[pDataWidthByte];
      
      
      ibSize = headerSizeRounded+payloadSize;
      ibHeaderSize = headerSize;      
      // Set segment and header size
      for (int i=0;i<2;i++)
        for (int j=0;j<8;j++)
        begin
          ibTransaction[0][i][j]   = ibSize[i*8+j];        // Set segment size
          ibTransaction[0][i+2][j] = ibHeaderSize[i*8+j];  // Set header size
        end  
      
      // Copy data from FL transaction to IB transaction
      wordNo = 0;
      byteNo = 4;
      // Copy header data
      for (int i=0;i<headerSize;i++)
      begin
        ibTransaction[wordNo][byteNo] = flTransaction.data[0][i];
        byteNo++;
        if (byteNo==pDataWidthByte) begin
          byteNo = 0;
          wordNo++;
        end  
      end  
        
      wordNo = headerSizeRounded/pDataWidthByte;
      byteNo = 0;
      // Copy payload data
      for (int i=0;i<payloadSize;i++)
      begin
        ibTransaction[wordNo][byteNo] = flTransaction.data[1][i];
        byteNo++;  
        if (byteNo==pDataWidthByte) begin
          byteNo = 0;
          wordNo++;
        end  
      end  
    endfunction : flTransactionToIbTransaction
    
    // ------------------------------------------------------------------------
    //! Put Into RAM 
    /*
     * Puts IB transaction into the RAM
     * \param ibTransaction - InternalBus transaction   
     * \param ifcNo - interface number         
     */      
    task putIntoRAM(byte ibTransaction[][], int ifcNo);

      // Copy data from IB transaction into the RAM
      for (int i=0;i<ibTransaction.size; i++)
      begin
        // Check fullness of SW Buffer
        while (((endPtr[ifcNo]+pDataWidthByte)%pBufferSize)==startPtr[ifcNo]) begin
          ibDownstream.sendStartPtrReq(ifcNo);  // Send Get Start Pointer request
          ibUpstream.receiveStrPtr(ifcNo, startPtr[ifcNo]);  // Wait for Start Pointer answer
        end

        // Copy data
        ram.storeBufferData(ifcNo,endPtr[ifcNo],ibTransaction[i]);
        
        // Increment end pointer
        endPtr[ifcNo]+=pDataWidthByte;                
        if (endPtr[ifcNo]==pBufferSize) 
          endPtr[ifcNo]=0;
      end  
     
      // Set new end pointer            
      ibDownstream.setTxEndPtr(endPtr[ifcNo], ifcNo); 
    endtask : putIntoRAM
    
    // -- Pause Controllers ---------------------------------------------------
    //! Pause controllers
    /*!
     * Pause all TX controllers at the same time or pause controllers randomly.
     */
    task pauseControllers();
      while (enabled && txPauseAllowed) begin
        int ifcNo;
        
        assert(randomize());           // Randomize rand variables

        // Wait between pausing
        repeat (pauseDelay) @(ibDownstream.ib_down.ib_down_cb);
        
        // -- Pause all TX controllers --
        if (txPauseAll) begin
          // Pause controllers
          for (int i=0; i<pFlows; i++) begin
            if (txCtrlStatus[i]==0) begin              
              fork
                automatic int j = i;   // Necessary for passing right parameter
                pauseController(j);
              join_none;
            end  
          end    
        end
        // -- Pause random TX controller --
        else begin
          ifcNo = $urandom_range(pFlows-1);
          if (txCtrlStatus[ifcNo]==0) begin
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
      txCtrlStatus[ifcNo]=1;
      
      // Wait while processing packet for corresponding interface
      while (inProcessing[ifcNo]) @(ibDownstream.ib_down.ib_down_cb);
      
      while (endPtr[ifcNo]!=startPtr[ifcNo]) begin
        ibDownstream.sendStartPtrReq(ifcNo);  // Send Get Start Pointer request
        ibUpstream.receiveStrPtr(ifcNo, startPtr[ifcNo]);  // Wait for Start Pointer answer
      end

      // Pause TX controller
      ibDownstream.pauseTxController(ifcNo);  
      
      // Pause time
      repeat (insidePauseDelay) @(ibDownstream.ib_down.ib_down_cb);

      // Unpause TX controller
      ibDownstream.unpauseTxController(ifcNo);  
      // Mark controller as unpaused
      txCtrlStatus[ifcNo] = 0;
    
    endtask : pauseController 
    
    // -- Stop Controllers ----------------------------------------------------
    //! Stop controllers
    /*!
     * Stop all TX controllers at the same time or stop controllers randomly.
     */
    task stopControllers();
      while (enabled && txStopAllowed) begin
        int ifcNo;
        
        assert(randomize());           // Randomize rand variables

        // Wait between pausing
        repeat (stopDelay) @(ibDownstream.ib_down.ib_down_cb);
        
        // -- Stop all TX controllers --
        if (txStopAll) begin
          // Stop controllers
          for (int i=0; i<pFlows; i++) begin
            if (txCtrlStatus[i]==0) begin              
              fork
                automatic int j = i;   // Necessary for passing right parameter
                stopController(j);
              join_none;
            end  
          end    
        end
        // -- Stop random TX controller --
        else begin
          ifcNo = $urandom_range(pFlows-1);
          if (txCtrlStatus[ifcNo]==0) begin
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
      txCtrlStatus[ifcNo]=1;
      
      // Wait while processing packet for corresponding interface
      while (inProcessing[ifcNo]) @(ibDownstream.ib_down.ib_down_cb);
      
      while (endPtr[ifcNo]!=startPtr[ifcNo]) begin
        ibDownstream.sendStartPtrReq(ifcNo);  // Send Get Start Pointer request
        ibUpstream.receiveStrPtr(ifcNo, startPtr[ifcNo]);  // Wait for Start Pointer answer
      end

      // Stop TX controller
      ibDownstream.stopTxController(ifcNo);  
      
      // Pause time
      repeat (insideStopDelay) @(ibDownstream.ib_down.ib_down_cb);

      // Set both start and end pointer to zero
      endPtr[ifcNo] = 0;
      ibDownstream.setTxEndPtr(endPtr[ifcNo], ifcNo);
      startPtr[ifcNo] = 0;
      ibDownstream.setTxStartPtr(startPtr[ifcNo], ifcNo);
      
      // Unstop TX controller
      ibDownstream.unstopTxController(ifcNo);  
      // Mark controller as unstopped
      txCtrlStatus[ifcNo] = 0;
    
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
    
endclass : RamDriver
