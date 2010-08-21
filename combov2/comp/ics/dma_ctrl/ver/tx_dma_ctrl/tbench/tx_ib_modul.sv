/*
 * tx_ib_driver.sv: InternalBus Driver for TX DMA Controller
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
 * $Id: tx_ib_modul.sv 8584 2009-06-01 14:39:20Z xsimko03 $
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  // -- InternalBus Driver Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to IB interface.  
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. 
   */
  class TxIbusModul #(int pDataWidth = 64, int pCtrlDmaDataWidth = 16, 
                     int pFlows = 2, int pPageSize = 4096, int pPageCount = 3);
    
    // -- Private Class Atributes --
    string    inst;                             // Driver identification
    bit       enabled;                          // Driver is enabled
    semaphore sem;                              // Semaphore solve problems with 
                                                     // concurent acces to mailbox   
    mailbox #(tDmaRequest) dmaMbx;              // Parsed DMA Request Mailbox
    virtual iDmaCtrl.dma_tb #(pCtrlDmaDataWidth) dma[pFlows];  
    virtual iInternalBus.ib_write_tb #(pDataWidth) ib;
    
    TxDmaModul #(pCtrlDmaDataWidth) dmaEngine[pFlows];      // DMA interface driver
    TxDmaCtrlDriver #(pDataWidth,pCtrlDmaDataWidth,pFlows,pPageSize,pPageCount) driver;
  
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create driver object 
    function new ( string inst,
                   TxDmaCtrlDriver #(pDataWidth,pCtrlDmaDataWidth,pFlows,pPageSize,pPageCount) driver, 
                   virtual iInternalBus.ib_write_tb #(pDataWidth) ib,
                   virtual iDmaCtrl.dma_tb #(pCtrlDmaDataWidth) dma[pFlows] 
                         );
      this.enabled     = 0;            // Driver is disabled by default
      this.inst        = inst;         // Store driver identifier
      this.driver      = driver;
      this.dma         = dma;          // Store pointer to DMA interface
      this.ib          = ib;           // Store pointer to IB interface

      this.dmaMbx  = new();
      this.sem     = new(1);
      
      // Create DMA Engine
      dmaEngine[0] = new("DmaEngine0", 0, this.dmaMbx, this.sem, dma[0]);
      dmaEngine[1] = new("DmaEngine1", 1, this.dmaMbx, this.sem, dma[1]);
      dmaEngine[2] = new("DmaEngine2", 2, this.dmaMbx, this.sem, dma[2]);
      dmaEngine[3] = new("DmaEngine3", 3, this.dmaMbx, this.sem, dma[3]);   
      
      // Initial values
      for (int i=0;i<pFlows;i++)
      begin
        this.dma[i].dma_cb.DMA_DONE   <= 0;
        this.dma[i].dma_cb.DMA_TAG    <= 0;
      end
      
      this.ib.ib_write_cb.WR_DATA <= 0;
      this.ib.ib_write_cb.WR_ADDR <= 0;
      this.ib.ib_write_cb.WR_REQ  <= 0;
      this.ib.ib_write_cb.WR_BE   <= 8'hFF;
         
    endfunction: new          
    
    // -- Enable Driver -------------------------------------------------------
    // Enable driver and runs driver process
    task setEnabled();
      enabled = 1; // Driver Enabling
      fork         
        run();     // Creating driver subprocess
      join_none;   // Don't wait for ending
      
      for(int i=0; i<pFlows; i++)       // DMA Engine enabling
        dmaEngine[i].setEnabled();
    endtask : setEnabled
        
    // -- Disable Driver ------------------------------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0; // Disable driver
      for(int i=0; i<pFlows; i++)       // DMA Engine disabling
        dmaEngine[i].setDisabled();
    endtask : setDisabled
  
    // -- Run Driver ----------------------------------------------------------
    // Take DMA Request from mailbox and put data from RAM into interface
    task run();
      while (enabled) begin            // Repeat while enabled        
        tDmaRequest parsedRequest;
        
        while (dmaMbx.num()==0) @(ib.ib_write_cb); // Wait until mailbox is not empty
        
        sem.get(1);                       // Lock
        dmaMbx.get(parsedRequest);        // Get Request from Mailbox
        sem.put(1);                       // Unlock
        
        sendTransaction(parsedRequest);   // Send Transaction
      end
    endtask : run
    
    // -- Send Transaction -----------------------------------------------------
    // Get data from RAM and send to IB interface
    task sendTransaction(tDmaRequest parsedRequest);
      logic[pDataWidth-1:0] data;
      int length;

      // Zero length means length of page size
      if (parsedRequest.length == 0) length = pPageSize/(pDataWidth/8);
      else length = parsedRequest.length/(pDataWidth/8);  

      for (int i=0; i<length; i++)
      begin
        waitForWrRdy();                        // Wait for WR_RDY
      
        // Get data from RAM
        driver.getData(parsedRequest.globalAddr+i*(pDataWidth/8), data);
        
        // Send data to interface
        ib.ib_write_cb.WR_DATA <= data;
        ib.ib_write_cb.WR_ADDR <= parsedRequest.localAddr+(pDataWidth/8)*i;
        ib.ib_write_cb.WR_REQ  <= 1;
        @(ib.ib_write_cb);
        ib.ib_write_cb.WR_REQ  <= 0;
      end
      
      // Send DMA_DONE
      dma[(parsedRequest.tag-1)/2].dma_cb.DMA_DONE  <= 1;
      dma[(parsedRequest.tag-1)/2].dma_cb.DMA_TAG   <= parsedRequest.tag;
      @(dma[(parsedRequest.tag-1)/2].dma_cb);
      dma[(parsedRequest.tag-1)/2].dma_cb.DMA_DONE  <= 0;
              
    endtask : sendTransaction
    
    // -- Wait For WR_RDY -----------------------------------------------------
    // Waits for WR_RDY
    task waitForWrRdy();
      while (!ib.ib_write_cb.WR_RDY) @(ib.ib_write_cb);
    endtask : waitForWrRdy

endclass : TxIbusModul
