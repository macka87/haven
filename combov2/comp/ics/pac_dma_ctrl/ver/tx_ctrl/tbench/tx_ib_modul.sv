/*
 * tx_ib_driver.sv: InternalBus Driver for TX PAC DMA Controller
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
 * $Id: tx_ib_modul.sv 10073 2009-08-05 09:13:48Z xsanta06 $
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
                      int pFlows = 2, int pNumFlags = 8, int pDmaTag = 0,
                      int pTransType = 0, int pRamSize = 4096, 
                      int pMaxDescLength = 1520);
    
    // -- Private Class Atributes --
    string    inst;                             // Driver identification
    bit       enabled;                          // Driver is enabled
    mailbox #(tDmaRequest) dmaMbx;              // Parsed DMA Request Mailbox
    virtual iInternalBus.ib_write_tb #(pDataWidth) ib;
    
    DmaModul #(pCtrlDmaDataWidth, pDmaTag, pTransType) dmaModul;  // DMA interface driver
    TxDmaCtrlDriver #(pFlows, pNumFlags, pRamSize, pMaxDescLength) driver;
  
    const int pDataWidthByte = pDataWidth/8;
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create driver object 
    function new ( string inst,
                   TxDmaCtrlDriver #(pFlows, pNumFlags, pRamSize, 
                                     pMaxDescLength) driver,
                   DmaModul #(pCtrlDmaDataWidth, pDmaTag, pTransType) dmaModul,
                   virtual iInternalBus.ib_write_tb #(pDataWidth) ib
                         );
      this.enabled     = 0;            // Driver is disabled by default
      this.inst        = inst;         // Store driver identifier
      this.driver      = driver;
      this.dmaModul    = dmaModul;
      this.ib          = ib;           // Store pointer to IB interface
      this.dmaMbx      = dmaModul.dmaMbx;       // Store pointer to mailbox
      
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
    endtask : setEnabled
        
    // -- Disable Driver ------------------------------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0; // Disable driver
    endtask : setDisabled
  
    // -- Run Driver ----------------------------------------------------------
    // Take DMA Request from mailbox and put data from RAM into interface
    task run();
      while (enabled) begin            // Repeat while enabled        
        tDmaRequest parsedRequest;

        // Wait until mailbox is not empty
        while (dmaMbx.num()==0) @(ib.ib_write_cb); 
        
        // Get Request from Mailbox
        dmaMbx.get(parsedRequest);
        
        // Send Transaction
        sendTransaction(parsedRequest);
      end
    endtask : run
    
    // -- Send Transaction -----------------------------------------------------
    // Get data from RAM and send to IB interface
    task sendTransaction(tDmaRequest parsedRequest);
      byte dataByte;
      logic[pDataWidth-1:0] data = 0;
      logic[7:0] byteEnable = 0;
      int offset = parsedRequest.localAddr % pDataWidthByte;
      int globalAddr = parsedRequest.globalAddr;
      int localAddr  = parsedRequest.localAddr - offset;

      $write("Getting from RAM - length:%0x; local:%0x; global:%0x\n",parsedRequest.length,localAddr,globalAddr); 
      
      // If data is smaller than one word
      if (offset+parsedRequest.length <= pDataWidthByte)
      begin
        $write("POSIELAM JEDINY BAJT\n");
        for (int i=offset; i<offset+parsedRequest.length; i++)
        begin
          // Get data from RAM
          driver.getDataByte(globalAddr, dataByte);

          for (int j=0; j<8; j++)
            data[i*pDataWidthByte+j] = dataByte[j];
          
          byteEnable[i] = 1;  

          globalAddr++;
        end   
      
        // Send data to interface
        ib.ib_write_cb.WR_DATA <= data;
        ib.ib_write_cb.WR_BE   <= byteEnable;
        ib.ib_write_cb.WR_ADDR <= localAddr;
        ib.ib_write_cb.WR_REQ  <= 1;
        @(ib.ib_write_cb);
        ib.ib_write_cb.WR_REQ  <= 0;
      
      end  
      // If data is bigger than one word
      else begin
        // -- Send first data word --
        // Wait for WR_RDY
        waitForWrRdy();
        // Send first word
        for (int i=offset; i<pDataWidthByte; i++)
        begin
          // Get data from RAM
          driver.getDataByte(globalAddr, dataByte);

          for (int j=0; j<8; j++)
            data[i*pDataWidthByte+j] = dataByte[j];
          
          byteEnable[i] = 1;  

          globalAddr++;
        end

        // Send data to interface
        ib.ib_write_cb.WR_DATA <= data;
        ib.ib_write_cb.WR_BE   <= byteEnable;
        ib.ib_write_cb.WR_ADDR <= localAddr;
        ib.ib_write_cb.WR_REQ  <= 1;
        @(ib.ib_write_cb);
        ib.ib_write_cb.WR_REQ  <= 0;

        localAddr += pDataWidthByte;

        // -- Send others data words
        for (int k=0; k<(parsedRequest.length-(pDataWidthByte-offset))/pDataWidthByte; k++)
        begin
          // Wait for WR_RDY
          waitForWrRdy();
        
          for (int i=0; i<pDataWidthByte; i++)
          begin
            // Get data from RAM
            driver.getDataByte(globalAddr, dataByte);

            for (int j=0; j<8; j++)
              data[i*pDataWidthByte+j] = dataByte[j];

            globalAddr++;
          end

          // Send data to interface
          ib.ib_write_cb.WR_DATA <= data;
          ib.ib_write_cb.WR_BE   <= 8'hFF;
          ib.ib_write_cb.WR_ADDR <= localAddr;
          ib.ib_write_cb.WR_REQ  <= 1;
          @(ib.ib_write_cb);
          ib.ib_write_cb.WR_REQ  <= 0;

          localAddr += pDataWidthByte;
          data = 0;
        end

        offset = (offset+parsedRequest.length)%pDataWidthByte;  
        byteEnable = 0;

        // -- Send last data word --
        if (offset != 0)
        begin
          // Wait for WR_RDY
          waitForWrRdy();
        
          for (int i=0; i<offset; i++)
          begin
            // Get data from RAM
            driver.getDataByte(globalAddr, dataByte);

            for (int j=0; j<8; j++)
              data[i*pDataWidthByte+j] = dataByte[j];

            byteEnable[i] = 1;  

            globalAddr++;
          end

          // Send data to interface
          ib.ib_write_cb.WR_DATA <= data;
          ib.ib_write_cb.WR_BE   <= byteEnable;
          ib.ib_write_cb.WR_ADDR <= localAddr;
          ib.ib_write_cb.WR_REQ  <= 1;
          @(ib.ib_write_cb);
          ib.ib_write_cb.WR_REQ  <= 0;
        end     
      end
      
      // Send DMA_DONE
      dmaModul.sendDmaDone(parsedRequest.tag);
                    
    endtask : sendTransaction
    
    // -- Wait For WR_RDY -----------------------------------------------------
    // Waits for WR_RDY
    task waitForWrRdy();
      while (!ib.ib_write_cb.WR_RDY) @(ib.ib_write_cb);
    endtask : waitForWrRdy

endclass : TxIbusModul
