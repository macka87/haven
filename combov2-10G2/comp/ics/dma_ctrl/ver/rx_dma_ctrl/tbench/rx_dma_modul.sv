/*
 * rx_dma_modul.sv: RX DMA Modul
 * Copyright (C) 2008 CESNET
 * Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
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
 * $Id: rx_dma_modul.sv 8583 2009-06-01 14:33:57Z xsimko03 $
 *
 * TODO:
 *
 */
  
  typedef struct{
    logic [64:0] global_addr;
    logic [32:0] local_addr;
    logic [12:0] length;
    logic [12:0] tag;
  } tParsedDMA;
  
  // --------------------------------------------------------------------------
  // -- DMA Modul Class
  // --------------------------------------------------------------------------
  /* This class is responsible for manipulating with transaction objects from 
   * DMA interface signals. Unit must be enabled by "setEnable()" function call.
   * Monitoring can be stoped by "setDisable()" function call.
   */
  class RxDmaModul #(int pCtrlDmaDataWidth = 16);
    
    // ----------------------
    // -- Class Attributes --
    // ----------------------
    string    inst;                             // Modul identification
    bit       enabled;                          // Modul is enabled
    int       ifcNo;                            // Number of connected interface
    semaphore sem;                              // Semaphore solve problems with 
                                                // concurent acces to mailbox   
    mailbox #(tParsedDMA) dmaMbx;               // Parsed DMA Request Mailbox
    int suma_dma=0; 
    
    virtual   iDmaCtrl.dma_tb #(pCtrlDmaDataWidth) dma_int;
       
    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create driver object 
    function new ( string inst, 
                   int ifcNo, 
                   mailbox #(tParsedDMA) dmaMbx,
                   semaphore sem,
                   virtual iDmaCtrl.dma_tb #(pCtrlDmaDataWidth) dma_int
                 );      
      this.enabled     = 0;            // Driver is disabled by default
      this.inst        = inst;         // Store modul identifier
      this.ifcNo       = ifcNo;        // Store interface number
      this.dmaMbx      = dmaMbx;       // Store pointer queue
      this.sem         = sem;
      this.dma_int     = dma_int;      // Store pointer interface 
      
      this.dma_int.dma_cb.DMA_ADDR  <=0;
      this.dma_int.dma_cb.DMA_ACK   <=0;
            
    endfunction: new 
    
    // -- Enable DMA -------------------------------------------
    // Enable DMA and runs DMA process
    task setEnabled();
      enabled = 1; // DMA Enabling
      fork         
        run();     // Creating driver subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable DMA ------------------------------------------
    // DMA Manager
    task setDisabled();
      enabled = 0; // DMA Disabling
    endtask : setDisabled
    
    // -- Run DMA Modul ------------------------------------------------------
    // Parsing of DMA 
    task run();
      while (enabled) begin                    // Repeat while enabled
        logic [127:0] dma;
        tParsedDMA parsedDma;
        receiveDMA(dma);
        parseDma(dma, parsedDma);
        add(parsedDma);        
      end
    endtask : run
    
    // -- Receive DMA ------------------------------------------------------
    // Receive DMA transaction from interface
    task receiveDMA(output logic [127:0] dma);
      logic [pCtrlDmaDataWidth-1:0] data_out;
      
      waitForDmaReq();
            
      for (int i=0; i<128/pCtrlDmaDataWidth; i++)begin
        dma_int.dma_cb.DMA_ADDR <= i;
        @(dma_int.dma_cb);
        data_out = dma_int.dma_cb.DMA_DOUT;
        
        for (int j=0; j<pCtrlDmaDataWidth; j++)
          dma[i*pCtrlDmaDataWidth+j] = data_out[j];
      end 
     
      dma_int.dma_cb.DMA_ACK <= 1;
      @(dma_int.dma_cb); 
      dma_int.dma_cb.DMA_ACK <= 0;     
    endtask : receiveDMA  
    
    // -- Wait For DMA REQ ----------------------------------------------------
    // Waits until DMA_REQ
    task waitForDmaReq();
      while (dma_int.dma_cb.DMA_REQ!=1) @(dma_int.dma_cb);
    endtask : waitForDmaReq
    
    // -- DMA parsing ---------------------------------------------------------
    task parseDma(logic [127:0] dma, output tParsedDMA parsedDma);
      logic [3:0] transType    = dma[3:0];  
      
      parsedDma.length=dma[15:4];          // length
      parsedDma.tag=dma[27:16];            // tag
      parsedDma.local_addr=dma[63:32];     // local address
      parsedDma.global_addr=dma[127:64];   // global address

      suma_dma+=parsedDma.length;
      //$write("DMA: length:   %d,tag:   %d, local:   %d, global:   %d,  SUMA:  %d\n",parsedDma.length,parsedDma.tag,parsedDma.local_addr,parsedDma.global_addr,suma_dma);
      
      if (transType!=1) begin
        $write ("Error in transitive part!!: %1d\n",transType);
        $stop;
      end  
      
      if (parsedDma.tag!=ifcNo*2+1) begin
        $write ("Error in tag : %1d\n",parsedDma.tag);
        $stop;
      end 
      
    endtask : parseDma
    
    // -- Add DMA ---------------------------------------------------------
    // Adds parsed DMA to fifo
    task add(tParsedDMA parsedDma);
      dmaMbx.put(parsedDma);
      sem.put(1);       // unlock
    endtask : add 
    
  endclass : RxDmaModul    
