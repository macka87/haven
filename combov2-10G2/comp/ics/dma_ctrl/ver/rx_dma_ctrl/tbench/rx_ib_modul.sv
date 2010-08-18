/*
 * rx_ibus_modul.sv: InternalBus Modul for RX DMA Controller
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
 * $$
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  // -- InternalBus Modul Class
  // --------------------------------------------------------------------------
  /* This class is responsible for manipulating with transaction objects from 
   * InternalBus interface signals. Unit must be enabled by "setEnable()" 
   * function call. Monitoring can be stoped by "setDisable()" function call.
   */
  class RxIbusModul #(int pDataWidth = 64, int pCtrlDmaDataWidth = 16, int pFlows=2,
                        int pPageSize = 4096, int pPageCount = 2);
    
    // ----------------------
    // -- Class Attributes --
    // ----------------------
    string    inst;                             // Modul identification
    bit       enabled;                          // Modul is enabled
    semaphore sem;                              // Semaphore solve problems with 
    logic[pDataWidth-1:0] ram[];                // concurent acces to mailbox   
    mailbox #(tParsedDMA) dmaMbx;               // Parsed DMA Request Mailbox  
    int suma_zapis=0;        
      
    RxDmaModul #(pCtrlDmaDataWidth) dma[pFlows];      // DMA interface monitor
        
    virtual iDmaCtrl.dma_tb #(pCtrlDmaDataWidth) dma_int[pFlows];
    virtual iInternalBus.ib_read_tb #(pDataWidth) ibus;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create driver object 
    function new ( string inst, 
                   virtual iInternalBus.ib_read_tb #(pDataWidth) ibus,
                   virtual iDmaCtrl.dma_tb #(pCtrlDmaDataWidth) dma_int[pFlows] 
                 );
      this.enabled     = 0;            // Modul is disabled by default
      this.inst        = inst;         // Store Modul identifier
      this.dma_int     = dma_int;
      this.ibus        = ibus;
      this.dmaMbx = new();
      this.sem    = new(1);
      
      dma[0] = new("DmaModul0", 0, this.dmaMbx, this.sem, dma_int[0]);
      dma[1] = new("DmaModul1", 1, this.dmaMbx, this.sem, dma_int[1]); 
      dma[2] = new("DmaModul0", 2, this.dmaMbx, this.sem, dma_int[2]);
      dma[3] = new("DmaModul1", 3, this.dmaMbx, this.sem, dma_int[3]); 
      
      ram    = new[pFlows*pPageCount*(pPageSize/(pDataWidth/8))]; 
            
      for (int i=0;i<pFlows;i++)begin
        this.dma_int[i].dma_cb.DMA_DONE   <= 0;
        this.dma_int[i].dma_cb.DMA_TAG    <= 0;
      end
      
      this.ibus.ib_read_cb.RD_ADDR     <= 0;
      this.ibus.ib_read_cb.RD_BE       <= 8'b11111111;
      this.ibus.ib_read_cb.RD_REQ      <= 0;
      this.ibus.ib_read_cb.RD_DST_RDY  <= 0;
      
    endfunction: new          
    
    // -- Enable Modul ------------------------------------------------------- 
    // Enable Modul and runs Modul process
    task setEnabled();
      enabled = 1; // Modul Enabling
      fork         
        run();     // Creating Modul subprocess
      join_none;   // Don't wait for ending
      
      for(int i=0; i<pFlows; i++)       // DMA Engine enabling
        dma[i].setEnabled();
    endtask : setEnabled
        
    // -- Disable Modul ------------------------------------------------------
    task setDisabled();
      enabled = 0; // Disable Modul
      for(int i=0; i<pFlows; i++)       // DMA Engine disabling
        dma[i].setDisabled();
    endtask : setDisabled

    // -- Get Data ------------------------------------------------------------
    // Get word of data from RAM
    task getData(int address, output byte unsigned data[]);
      data = new[pDataWidth/8];
      
      for (int i=0;i<(pDataWidth/8);i++)
        for (int j=0;j<8;j++)
          data[i][j] = ram[address][i*(pDataWidth/8)+j];
    endtask : getData
  
    // -- Run Modul ----------------------------------------------------------
    task run();
      logic[pDataWidth-1:0] ibus_transaction[];
      tParsedDMA parsedDma;
      while (enabled) begin                     // Repeat while enabled        
        while (dmaMbx.num()==0) @(ibus.ib_read_cb);
        sem.get(1);
        dmaMbx.get(parsedDma);                  // Get Request from Mailbox
        sem.put(1);
	setIbus(parsedDma,ibus_transaction);    // Set Internal Bus signals and put data into RAM
      end
    endtask : run
    
    // -- Setting of InternalBus Signals
    task setIbus(tParsedDMA parsedDma, output logic[pDataWidth-1:0] ram_data[]);
      int local_addr=parsedDma.local_addr;
      longint global=parsedDma.global_addr/(pDataWidth/8);
      logic [pDataWidth-1:0] data;
      int cnt=0;
      int m=0;
      int boundary;
      int ifcNo=parsedDma.tag/2;
      
      // Zero length means length of page size 
      if (parsedDma.length == 0) boundary = pPageSize/(pDataWidth/8);
      else boundary = parsedDma.length/(pDataWidth/8);

      ibus.ib_read_cb.RD_DST_RDY  <= 1;
      @(ibus.ib_read_cb);
      
      do begin
        ibus.ib_read_cb.RD_ADDR <= local_addr;
        ibus.ib_read_cb.RD_REQ  <= 1;
        @(ibus.ib_read_cb);
        ibus.ib_read_cb.RD_REQ  <= 0;
        waitForSrc(); 
        data = ibus.ib_read_cb.RD_DATA; 
        suma_zapis+=8;
        //$write("IB MODUL: Adresa pri zapise do RAM: %d\n",global);
        //$write("IB MODUL: Zapisovane data do RAM: %x\n",data);
        ram[global]=data;
        cnt++;  
        local_addr+=8; 
        global++;
      end while(cnt!=boundary);
      
      dma_int[ifcNo].dma_cb.DMA_DONE  <= 1;
      dma_int[ifcNo].dma_cb.DMA_TAG  <= parsedDma.tag;
      @(dma_int[ifcNo].dma_cb);
      dma_int[ifcNo].dma_cb.DMA_DONE  <= 0;
    endtask : setIbus
    
    // -- Wait for RD_SRC_RDY --------------------------------------------------
    task waitForSrc(); 
      do begin
        @(ibus.ib_read_cb);
      end while (ibus.ib_read_cb.RD_SRC_RDY==0); 
    endtask : waitForSrc
   
  endclass : RxIbusModul 
