/*
 * rx_desc_manager.sv: Descriptor manager for RX DMA Controller
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
 * $Id: rx_desc_manager.sv 8583 2009-06-01 14:33:57Z xsimko03 $
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  // -- Descriptor Manager Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to descriptor FIFO 
   * interface. Descriptors are stored by 'descQue'(Queue) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. 
   */
  class RxDescManager #(int pCtrlDmaDataWidth = 16, int pFlows = 2, int pPageSize = 4096, int pPageCount = 2);
    
    // -----------------------------
    // -- Private Class Atributes --
    // -----------------------------
    string  inst;                               // Modul identification
    bit  enabled;                               // Modul is enabled
    logic[63:0]  descQue[$];                    // Descriptors Queue
    logic[63:0]  descriptor[];                  // Descriptors for each flow
    int  ifcNo;                                 // Interface number 

    // Descriptor Manager interface    
    virtual iDmaCtrl.desc_tb #(pCtrlDmaDataWidth) desc;
    
    // -------------------
    // -- Class Methods --
    // -------------------
    
    // -- Constructor ---------------------------------------------------------
    // Create Descriptor Manager object 
    function new ( string inst, 
                   virtual iDmaCtrl.desc_tb #(pCtrlDmaDataWidth) desc,
                   int ifcNo
                   );
      int pageSizeCounter; 
      
      this.enabled     = 0;            // Modul is disabled by default
      this.inst        = inst;         // Store Modul identifier
      this.desc        = desc;         // Store pointer interface 
      this.ifcNo       = ifcNo;        // Interface number 
      
      this.desc.desc_cb.DESC_DO    <= 0;
      this.desc.desc_cb.DESC_EMPTY <= 1;

      for (int i=0;i<pFlows;i++)
        if (ifcNo==i) pageSizeCounter=i*pPageSize;
   
      descriptor = new[pPageCount];
      
      // Set descriptors for each page   
      for(int i=0; i<pPageCount; i++)begin
        descriptor[i]=pageSizeCounter;
        pageSizeCounter += pFlows*pPageSize;
      end

    endfunction: new          
    
    // -- Enable Descriptor Manager -------------------------------------------
    // Enable Descriptor Manager and runs Descriptor Manager process
    task setEnabled();
      enabled = 1; // Descriptor Manager Enabling
      fork         
        run();     // Creating Modul subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Descriptor Manager ------------------------------------------
    // Disable Descriptor Manager
    task setDisabled();
      enabled = 0; // Descriptor Manager Disabling
    endtask : setDisabled
  
    // -- Run Descriptor Manager ----------------------------------------------
    // Take descriptor from queue and generate them to interface
    task run();
      int page=1;
      while (enabled) begin                    // Repeat while enabled        
        waitForNotEmpty();                     // Set DESC_EMPTY
        sendDescriptor(descQue.pop_front());   // Send Descriptor
        addDescriptor(descriptor[page]);       // Add Descriptor to gueue
        page++;
        if (page==pPageCount) page=0;
      end
    endtask : run
    
    // -- Wait For Not Empty --------------------------------------------------
    // Waits while descQue is empty
    task waitForNotEmpty();
      desc.desc_cb.DESC_EMPTY <= 1;
      while (!descQue.size()) @(desc.desc_cb);
      desc.desc_cb.DESC_EMPTY <= 0;
    endtask : waitForNotEmpty
    
    // -- Send Descriptor -----------------------------------------------------
    // Sets DESC_DO and wait until DESC_READ
    task sendDescriptor(logic[63:0] descriptor);
      logic [pCtrlDmaDataWidth:0] data;
      
      for (int i=0; i<64/pCtrlDmaDataWidth;i++)begin
        for (int j=0; j<pCtrlDmaDataWidth; j++)
          data[j] = descriptor[i*pCtrlDmaDataWidth+j];
        desc.desc_cb.DESC_DO <= data;
        @(desc.desc_cb);
        waitForDescRead();
      end
    endtask : sendDescriptor
    
    // -- Wait For Desc Read --------------------------------------------------
    // Waits until DESC_READ
    task waitForDescRead();
      while (!desc.desc_cb.DESC_READ) 
        @(desc.desc_cb);
    endtask : waitForDescRead
    
    // -- Add Descriptor ------------------------------------------------------
    // Adds descriptor do queue
    task addDescriptor(logic[63:0] descriptor);
      // display which descriptor was added
      // $write("added descriptor:%d\n",descriptor);
      // descriptor is sent to que
      descQue.push_back(descriptor);
    endtask : addDescriptor  
    
  endclass : RxDescManager
