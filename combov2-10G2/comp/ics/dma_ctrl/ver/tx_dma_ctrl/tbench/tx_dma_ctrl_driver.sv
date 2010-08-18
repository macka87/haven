/*
 * tx_dma_ctrl_driver.sv: TX DMA Controller Driver
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
 * $Id: tx_dma_ctrl_driver.sv 12979 2010-02-26 16:13:08Z kastovsky $
 *
 * TODO:
 *
 */
 
  import sv_tx_dma_ctrl_pkg::*;
   
  // --------------------------------------------------------------------------
  // -- TX DMA Controller Driver Class
  // --------------------------------------------------------------------------
  /* This class is responsible for simulating software buffer in RAM.  
   * Transactions are received by 'transMbx'(Mailbox) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. 
   */
  class TxDmaCtrlDriver #(int pDataWidth = 64, int pCtrlDmaDataWidth = 16, 
                          int pFlows = 2, int pPageSize = 4096, int pPageCount = 3);
    
    // ----------------------
    // -- Class Attributes --
    // ----------------------
    string    inst;                             // Driver identification
    bit       enabled;                          // Driver is enabled
    tTransMbx transMbx;                         // Transaction mailbox
    DriverCbs cbs[$];                           // Callbacks list
    
    TxSoftwareModul #(pFlows,pPageSize,pPageCount) swDriver;    // MI32 interface driver
    TxDescManager #(pCtrlDmaDataWidth) descManager[pFlows];      // Descriptor interface driver
    
    int startPtr[]     = new [pFlows];          // Start pointers for each flow
    int endPtr[]       = new [pFlows];          // End pointers for each flows 
    logic[63:0] descriptor[][];                 // Descriptors for each flow
    byte ram[][];                               // Software memory
    
    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create driver object 
    function new ( string inst, 
                   tTransMbx transMbx,
                   virtual iMi32.tb mi32,
                   virtual iDmaCtrl.desc_tb #(pCtrlDmaDataWidth) desc[pFlows] 
                   );
      int pageSizeCounter = 0;
      
      this.enabled     = 0;            // Driver is disabled by default
      this.transMbx    = transMbx;     // Store pointer to mailbox
      this.inst        = inst;         // Store driver identifier
      swDriver = new("SwDriver", mi32);
      descManager[0] = new("DescManager0", desc[0]);
      descManager[1] = new("DescManager1", desc[1]);
      descManager[2] = new("DescManager2", desc[2]);
      descManager[3] = new("DescManager3", desc[3]);
      
      
      // Allocate memory for descriptors and RAM
      descriptor = new[pFlows];
      ram        = new[pFlows*pPageCount*(pPageSize/(pDataWidth/8))];
      foreach(descriptor[i]) descriptor[i] = new[pPageCount];
      foreach(ram[i]) ram[i] = new[pDataWidth/8];

      // Initiate start and end pointer for each flow
      for(int i=0; i<pFlows; i++)
      begin
        startPtr[i] = 0;
        endPtr[i]   = 0;
      end
      
      // Set descriptors for each flow  
      for(int i=0; i<pPageCount; i++)
        for(int j=0; j<pFlows; j++)
        begin
          descriptor[j][i]=pageSizeCounter;
          pageSizeCounter += pPageSize/(pDataWidth/8);
        end
    
    endfunction: new          
    
    // -- Set Callbacks -------------------------------------------------------
    // Put callback object into List 
    function void setCallbacks(DriverCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks
    
    // -- Enable Driver -------------------------------------------------------
    // Enable driver and runs driver process
    task setEnabled();
      enabled = 1; // Driver Enabling
      fork         
        run();     // Creating driver subprocess
      join_none;   // Don't wait for ending
      
      for(int i=0; i<pFlows; i++)       // Descriptor manager enabling
        descManager[i].setEnabled();
    endtask : setEnabled
        
    // -- Disable Driver ------------------------------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0; // Disable driver, after sending last transaction it ends
//      ramDisplay();
      for(int i=0; i<pFlows; i++)       // Descriptor manager disabling
        descManager[i].setDisabled();
    endtask : setDisabled
  
    // -- Get Data ------------------------------------------------------------
    // Get word of data from RAM
    task getData(int address, output logic[pDataWidth-1:0] data);
//      $write("OUTPUT FROM GET DATA: addr:%1x\n", address);
      
      for (int i=0; i<pDataWidth/8; i++)
        for (int j=0; j<8; j++)
          data[i*8+j] = ram[address/(pDataWidth/8)][i][j];
    endtask : getData
    
    // -- Run Driver ----------------------------------------------------------
    // Take transactions from mailbox and put them into ram
    task run();
      FrameLinkTransaction transaction;
      Transaction to;
      swDriver.initCtrl();             // Wait until SW Driver finishes initialization
      while (enabled) begin            // Repeat while enabled        
        transMbx.get(to);              // Get transaction from mailbox
        $cast(transaction,to);
        assert(randomize());
        putTransaction(transaction);   // Send Transaction
        // Call transaction postprocesing, if is available
        foreach (cbs[i]) cbs[i].post_tx(to, inst);
      end
    endtask : run
    
    // -- Put Transaction -----------------------------------------------------
    // 
    task putTransaction(FrameLinkTransaction flTransaction);
      byte ibTransaction[][];
      
      //flTransaction.display("FL Transaction");
      flTransactionToIbTransaction(flTransaction, ibTransaction);
//      ibDisplay(ibTransaction);
      
      putIntoRAM(ibTransaction, flTransaction.ifcNo);
      
    endtask : putTransaction
    
    // -- FL Transaction to IB Transaction ------------------------------------
    // Makes IB transaction from FL transaction
    task flTransactionToIbTransaction(FrameLinkTransaction flTransaction,
                                      output byte ibTransaction[][]);
      int headerSize  = flTransaction.data[0].size;  // Header data size
      int headerSizeRounded = headerSize+4;
      int payloadSize = flTransaction.data[1].size;  // Payload data size
      int payloadSizeRounded = payloadSize;
      logic [15:0] ibSize, ibHeaderSize;
      int wordNo, byteNo;                            // Offset in ibTransaction
            
      // Get rounded header size
      if ((headerSize+4)%(pDataWidth/8)!=0) 
        headerSizeRounded = ((headerSize+4)/(pDataWidth/8)+1)*(pDataWidth/8);
      
      // Get rounded payload size
      if (payloadSize%(pDataWidth/8)!=0) 
        payloadSizeRounded = (payloadSize/(pDataWidth/8)+1)*(pDataWidth/8);
      
      // Allocate space for new IB transaction
      ibTransaction = new[(headerSizeRounded+payloadSizeRounded)/(pDataWidth/8)];
      foreach(ibTransaction[i]) ibTransaction[i] = new[pDataWidth/8];
      
      
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
        if (byteNo==pDataWidth/8) begin
          byteNo = 0;
          wordNo++;
        end  
      end  
        
      wordNo = headerSizeRounded/(pDataWidth/8);
      byteNo = 0;
      // Copy payload data
      for (int i=0;i<payloadSize;i++)
      begin
        ibTransaction[wordNo][byteNo] = flTransaction.data[1][i];
        byteNo++;  
        if (byteNo==pDataWidth/8) begin
          byteNo = 0;
          wordNo++;
        end  
      end  
    
    endtask : flTransactionToIbTransaction
    
    // -- Put Into RAM --------------------------------------------------------
    // Puts IB transaction into the RAM
    task putIntoRAM(byte ibTransaction[][], int ifcNo);
      int descNo;
      int pageOffset;

      // Copy data from IB transaction into the RAM
      for (int i=0;i<ibTransaction.size; i++)
      begin
        // Check fullness of SW Buffer
        while (((endPtr[ifcNo]+1)%(pPageCount*(pPageSize/(pDataWidth/8))))==startPtr[ifcNo]) begin
          swDriver.getStrPtr(ifcNo, startPtr[ifcNo]);
          startPtr[ifcNo]=startPtr[ifcNo]/(pDataWidth/8);
//          ramDisplay();
          end
        
        descNo = endPtr[ifcNo]/(pPageSize/(pDataWidth/8));
        pageOffset = endPtr[ifcNo]%(pPageSize/(pDataWidth/8));
        //$write("tok: %d\n", ifcNo);
        // Send descriptor if new page starts
        if (pageOffset==0) 
          descManager[ifcNo].addDescriptor(descriptor[ifcNo][descNo]*(pDataWidth/8));        

        // Copy data
        ram[pageOffset+descriptor[ifcNo][descNo]] = ibTransaction[i];
        
        // Increment end pointer
        endPtr[ifcNo]++;                
        if (endPtr[ifcNo]==pPageCount*(pPageSize/(pDataWidth/8))) 
          endPtr[ifcNo]=0;
      end  
     
      // Set new end pointer            
      swDriver.setEndPtr(ifcNo, endPtr[ifcNo]*(pDataWidth/8)); 
      
    endtask : putIntoRAM
    
    // -- Display functions -----------
    
    // -- IB Display ----------------------------------------------------------
    // Displays IB transaction
    task ibDisplay(byte ibTransaction[][]);
      $write ("-----------------------------------\n");
      $write ("-- IB Transaction\n");
      $write ("-----------------------------------\n");
      
      for (int i=0; i<ibTransaction.size; i++)
      begin
        for (int j=0; j<ibTransaction[i].size; j++)
          $write ("%x",ibTransaction[i][j]);
        $write("\n");
      end       
    endtask : ibDisplay  
    
    // -- RAM Display ---------------------------------------------------------
    // Displays RAM content
    task ramDisplay();
      $write ("-----------------------------------\n");
      $write ("-- DESCRIPTORS\n");
      $write ("-----------------------------------\n");
      
      for(int i=0; i<descriptor.size;i++)
      begin
        $write("IFC NO: %1d\n",i);
        for(int j=0; j<descriptor[i].size;j++)
          $write("%1d == %1x\n", descriptor[i][j],descriptor[i][j]);
      end    
      
      $write ("-----------------------------------\n");
      $write ("-- RAM\n");
      $write ("-----------------------------------\n");
      
      for (int i=0; i<ram.size; i++)
      begin
        if (i%(pPageSize/(pDataWidth/8))==0) $write("\n\n");
        $write("%4x: ",i*(pDataWidth/8));
        for (int j=0; j < ram[i].size; j++)
          $write("%x ",ram[i][j]);
        $write("\n");
      end 
      $write ("-----------------------------------\n"); 
    endtask : ramDisplay
    
endclass : TxDmaCtrlDriver
