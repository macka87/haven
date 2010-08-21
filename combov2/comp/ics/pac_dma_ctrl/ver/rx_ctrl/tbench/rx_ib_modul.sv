/*
 * rx_ibus_modul.sv: InternalBus Modul for RX DMA Controller
 * Copyright (C) 2009 CESNET
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
 
  import sv_rx_pac_dma_ctrl_pkg::*;
  // --------------------------------------------------------------------------
  // -- InternalBus Modul Class
  // --------------------------------------------------------------------------
  /* This class is responsible for manipulating with transaction objects from 
   * InternalBus interface signals. Unit must be enabled by "setEnable()" 
   * function call. Monitoring can be stoped by "setDisable()" function call.
   */
  class RxIbusModul #(int pDataWidth = 64, int pCtrlDmaDataWidth = 16, int pFlows=2,
                      int pRamSize = 1024, int pDmaTag = 0, int pTransType = 0);
    
    // ----------------------
    // -- Class Attributes --
    // ----------------------
    string    inst;                             // Modul identification
    bit       enabled;                          // Modul is enabled
    logic[pDataWidth-1:0] ram[];                // Concurent acces to mailbox   
    mailbox #(tDmaRequest) dmaMbx;              // Parsed DMA request mailbox  
          
    DmaModul #(pCtrlDmaDataWidth, pDmaTag, pTransType) dma;   // DMA interface monitor
        
    virtual iInternalBus.ib_read_tb #(pDataWidth) ibus;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create driver object 
    function new ( string inst, 
                   DmaModul #(pCtrlDmaDataWidth, pDmaTag, pTransType) dma,
                   virtual iInternalBus.ib_read_tb #(pDataWidth) ibus
                  );
      this.enabled     = 0;            // Modul is disabled by default
      this.inst        = inst;         // Store modul identifier
      this.dma         = dma;          // DMA modul 
      this.ibus        = ibus;         // IB modul 
      this.dmaMbx      = dma.dmaMbx;   // Store pointer to mailbox
            
      ram    = new[pRamSize]; 
            
      this.ibus.ib_read_cb.RD_ADDR     <= 0;
      this.ibus.ib_read_cb.RD_BE       <= 8'b11111111;
      this.ibus.ib_read_cb.RD_REQ      <= 0;
      this.ibus.ib_read_cb.RD_DST_RDY  <= 0;
      
    endfunction: new          
    
    // -- Enable Modul ------------------------------------------------------- 
    // Enable Modul and runs Modul process
    task setEnabled();
      enabled = 1;              // Modul enabling
      fork         
        run();                  // Creating modul subprocess
      join_none;                // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Modul ------------------------------------------------------
    task setDisabled();
      enabled = 0;              // Disable Modul
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
      tDmaRequest parsedDma;
      while (enabled) begin                             // Repeat while enabled        
        while (dmaMbx.num()==0) @(ibus.ib_read_cb);     // Wait if Mailbox is empty
         dmaMbx.get(parsedDma);                         // Get request from Mailbox
        setIbus(parsedDma,ibus_transaction);            // Set Internal Bus signals and put data into RAM
      end
    endtask : run
    
    // -- Setting of InternalBus Signals
    task setIbus(tDmaRequest parsedDma, output logic[pDataWidth-1:0] ram_data[]);
      int local_addr=parsedDma.localAddr;                       // Local address in HW
      longint global=parsedDma.globalAddr/(pDataWidth/8);       // Global address in RAM
      logic [pDataWidth-1:0] data;
      int cnt=0;                                                // Counter of (pDataWidth/8) words
      int boundary;                                             // Transaction size in words
      int ifcNo=parsedDma.tag/2;                                // Interface number
      
      // Zero length means length of page size 
      boundary = parsedDma.length/(pDataWidth/8);
      if((parsedDma.length%(pDataWidth/8))>0) boundary++;

      ibus.ib_read_cb.RD_DST_RDY  <= 1;
      @(ibus.ib_read_cb);
      
      // Set values of InternalBus signals
      do begin
        ibus.ib_read_cb.RD_ADDR <= local_addr;
        ibus.ib_read_cb.RD_REQ  <= 1;
        @(ibus.ib_read_cb);
        ibus.ib_read_cb.RD_REQ  <= 0;
        waitForSrc(); 
        data = ibus.ib_read_cb.RD_DATA; 
        //$write("IB MODUL: Adresa pri zapise do RAM: %d\n",global);
        //$write("IB MODUL: Zapisovane data do RAM: %x\n",data);
        ram[global]=data;
        cnt++;  
        local_addr+=8; 
        global++;
      end while(cnt!=boundary);
      
      // Send DMA_DONE
      dma.sendDmaDone(parsedDma.tag);
    endtask : setIbus
    
    // -- Wait for RD_SRC_RDY --------------------------------------------------
    task waitForSrc(); 
      do begin
        @(ibus.ib_read_cb);
      end while (ibus.ib_read_cb.RD_SRC_RDY==0); 
    endtask : waitForSrc
   
  endclass : RxIbusModul 
