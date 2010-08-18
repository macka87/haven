/*
 * tx_desc_manager.sv: Descriptor manager for TX DMA Controller
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
 * $Id: tx_desc_manager.sv 8584 2009-06-01 14:39:20Z xsimko03 $
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  // -- Descriptor manager Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to descriptor FIFO 
   * interface. Descriptors are stored by 'descQue'(Queue) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. 
   */
  class TxDescManager #(int pCtrlDmaDataWidth = 16);
    
    // -----------------------------
    // -- Private Class Atributes --
    // -----------------------------
    string       inst;                             // Driver identification
    bit          enabled;                          // Driver is enabled
    logic[63:0]  descQue[$];                       // Descriptors Queue
    virtual iDmaCtrl.desc_tb #(pCtrlDmaDataWidth) desc;
    
    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create Descriptor Manager object 
    function new ( string inst, 
                   virtual iDmaCtrl.desc_tb #(pCtrlDmaDataWidth) desc
                   );      
      this.enabled     = 0;            // Driver is disabled by default
      this.inst        = inst;         // Store driver identifier
      this.desc        = desc;         // Store pointer interface 
      
      this.desc.desc_cb.DESC_DO    <= 0;
      this.desc.desc_cb.DESC_EMPTY <= 1;
      
    endfunction: new          
    
    // -- Enable Descriptor Manager -------------------------------------------
    // Enable Descriptor Manager and runs Descriptor Manager process
    task setEnabled();
      enabled = 1; // Descriptor Manager Enabling
      fork         
        run();     // Creating driver subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Descriptor Manager ------------------------------------------
    // Disable Descriptor Manager
    task setDisabled();
      enabled = 0; // Descriptor Manager Disabling
      desc.desc_cb.DESC_EMPTY <= 1;
    endtask : setDisabled
  
    // -- Add Descriptor ------------------------------------------------------
    // Adds descriptor do queue
    task addDescriptor(logic[63:0] descriptor);
      descQue.push_back(descriptor);
    endtask : addDescriptor  
    
    // -- Run Descriptor Manager ----------------------------------------------
    // Take descriptor from queue and generate them to interface
    task run();
      while (enabled) begin                    // Repeat while enabled        
        waitForNotEmpty();                     // Set DESC_EMPTY
        sendDescriptor(descQue.pop_front());   // Send Descriptor
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

      for (int i=0; i<64/pCtrlDmaDataWidth;i++)
      begin
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
    
endclass : TxDescManager
