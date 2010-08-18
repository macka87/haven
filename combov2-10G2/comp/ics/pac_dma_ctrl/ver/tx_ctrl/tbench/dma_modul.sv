/*
 * dma_modul.sv: DMA Engine for PAC DMA Controller
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
 * $Id: dma_modul.sv 10802 2009-08-26 14:42:19Z xsanta06 $
 *
 * TODO:
 *
 */
  
  // Parsed DMA Request structure
  typedef struct{
    logic [11:0] length;
    logic [11:0] tag;
    logic [31:0] localAddr;
    logic [63:0] globalAddr;
  } tDmaRequest;  
  
  // --------------------------------------------------------------------------
  // -- DMA Engine Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to DMA interface and 
   * parsing DMA Requests. Unit must be enabled by "setEnable()" function call.
   * Generation can be stoped by "setDisable()" function call. 
   */
  class DmaModul #(int pCtrlDmaDataWidth = 16, int pDmaTag = 2, 
                   int pTransType = 0);
    
    // -- Private Class Atributes --
    string    inst;                             // Engine identification
    bit       enabled;                          // Engine is enabled
    int       ifcNo;                            // Number of connected interface
    mailbox #(tDmaRequest) dmaMbx;              // Parsed DMA Request Mailbox
    virtual iDmaCtrl.dma_tb #(pCtrlDmaDataWidth) dma;

    
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create DMA Engine object 
    function new ( string inst,
                   virtual iDmaCtrl.dma_tb #(pCtrlDmaDataWidth) dma
                         );      
      this.enabled     = 0;            // Engine is disabled by default
      this.inst        = inst;         // Store engine identifier
      this.ifcNo       = ifcNo;        // Store interface number
      this.dma         = dma;          // Store pointer interface 

      // Initial values
      this.dma.dma_cb.DMA_ADDR   <= 0;
      this.dma.dma_cb.DMA_ACK    <= 0;
      this.dma.dma_cb.DMA_DONE   <= 0;
      this.dma.dma_cb.DMA_TAG    <= 0;
      
      this.dmaMbx      = new(0);
    endfunction: new          
    
    // -- Enable DMA Engine ---------------------------------------------------
    // Enable DMA Engine and runs DMA Engine process
    task setEnabled();
      enabled = 1; // DMA Engine Enabling
      fork         
        run();     // Creating engine subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable DMA Engine --------------------------------------------------
    // Disable DMA Engine
    task setDisabled();
      enabled = 0; // DMA Engine Disabling
    endtask : setDisabled
  
    
    // -- Private Class Methods --
    
    // -- Run DMA Engine ------------------------------------------------------
    // Parse DMA Request and store it in queue
    task run();
      while (enabled) begin                    // Repeat while enabled
        logic [127:0] dmaRequest;
        tDmaRequest parsedRequest;
        
        getDmaRequest(dmaRequest);                     // Get DMA Request from interface
        //$write("DMA POZIADAVKA:   %x\n",dmaRequest);
        parseDmaRequest(dmaRequest, parsedRequest);    // Parse DMA Request
        addRequest(parsedRequest);                     // Add parsed DMA request into mailbox
      end
    endtask : run
        
    // -- Get DMA Request -----------------------------------------------------
    // Gets DMA Request from interface
    task getDmaRequest(output logic [127:0] dmaRequest);
      logic [pCtrlDmaDataWidth-1:0] requestPart;
      
      waitForDmaReq();                    // Waits until DMA_REQ
      
      // Process whole DMA Request
      for (int i=0; i<128/pCtrlDmaDataWidth; i++)
      begin
        dma.dma_cb.DMA_ADDR <= i;
        @(dma.dma_cb);
        requestPart = dma.dma_cb.DMA_DOUT;
        
        for (int j=0; j<pCtrlDmaDataWidth; j++)
          dmaRequest[i*pCtrlDmaDataWidth+j] = requestPart[j];
      end 
      
      // Set DMA_ACK
      dma.dma_cb.DMA_ACK <= 1;
      @(dma.dma_cb);
      dma.dma_cb.DMA_ACK <= 0;
         
    endtask : getDmaRequest
    
    // -- Parse DMA Request ---------------------------------------------------
    // Parse DMA Request and store it in struct
    task parseDmaRequest(logic [127:0] dmaRequest, output tDmaRequest parsedRequest);
      logic [3:0] transType    = dmaRequest[3:0];
              
      // Parse DMA Request
      parsedRequest.length     = dmaRequest[15:4];
      parsedRequest.tag        = dmaRequest[27:16];
      parsedRequest.localAddr  = dmaRequest[63:32];
      parsedRequest.globalAddr = dmaRequest[127:64];

      display(parsedRequest, transType);
      
      //Check Trans Type
      assert (transType==pTransType) 
      else $error("Incorrect transType: %0d",transType);

      // Check Tag
      assert (parsedRequest.tag[1:0]==pDmaTag)
      else $error("Incorrect tag: %0d",parsedRequest.tag);
    
    endtask : parseDmaRequest  
    
    // -- Wait For DMA REQ ----------------------------------------------------
    // Waits until DMA_REQ
    task waitForDmaReq();
      while (!dma.dma_cb.DMA_REQ) @(dma.dma_cb);
    endtask : waitForDmaReq
    
    // -- Add Request ---------------------------------------------------------
    // Adds parsed DMA Request to queue
    task addRequest(tDmaRequest parsedRequest);
      dmaMbx.put(parsedRequest);
    endtask : addRequest  
   
    
    // -- Public Class Methods --
    
    // -- Send Dma Done -------------------------------------------------------
    // Sets dmaDone flag
    task sendDmaDone(logic [11:0] tag);
      dma.dma_cb.DMA_DONE  <= 1;
      dma.dma_cb.DMA_TAG   <= tag;
      @(dma.dma_cb);
      dma.dma_cb.DMA_DONE  <= 0;
    endtask : sendDmaDone  
    
    // -- Display -------------------------------------------------------------
    // Adds parsed DMA Request to queue
    task display(tDmaRequest parsedRequest, int transType);
      $write("---------------------------------------------------------\n");
      $write("-- DMA Request\n");
      $write("---------------------------------------------------------\n");
      $write("Type:%0x Length:%0x Tag:%0x LocalAddr:%0x GlobalAddr:%0x\n",transType,parsedRequest.length,parsedRequest.tag,parsedRequest.localAddr,parsedRequest.globalAddr);
    endtask : display 
   
endclass : DmaModul
