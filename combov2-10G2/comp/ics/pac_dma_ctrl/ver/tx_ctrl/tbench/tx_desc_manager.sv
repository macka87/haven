/*
 * tx_desc_manager.sv: Descriptor manager for TX PAC DMA Controller
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
 * $Id: tx_desc_manager.sv 9399 2009-07-14 19:51:39Z xsanta06 $
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
  class TxDescManager #(int pFlows = 2);
    
    // -----------------------------
    // -- Private Class Atributes --
    // -----------------------------
    string       inst;                             // Manager identification
    bit          enabled;                          // Manager is enabled
    logic[63:0]  descQue[pFlows][$];               // Descriptors Queue
    virtual iPacDmaCtrl.desc_tb #(pFlows) desc;

    // ----
    rand bit enDelay;   // Enable/Disable DO_VLD delay
      // Enable/Disable DO_VLD delay (weights)
      int delayEn_wt             = 1; 
      int delayDisable_wt        = 3;

    rand int delay; // DO_VLD delay
      // DO_VLD delay limits
      int delayLow          = 0;
      int delayHigh         = 3;
    // ----
    
    // -- Constrains --
    constraint cDelays {
      enDelay dist { 1'b1 := delayEn_wt,
                     1'b0 := delayDisable_wt
                   };

      delay inside {
                    [delayLow:delayHigh]
                   };
      }
   
    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create Descriptor Manager object 
    function new ( string inst, 
                   virtual iPacDmaCtrl.desc_tb #(pFlows) desc
                   );      
      this.enabled     = 0;            // Manager is disabled by default
      this.inst        = inst;         // Store manager identifier
      this.desc        = desc;         // Store pointer interface 
      
      this.desc.desc_cb.DESC_DO     <= 0;
      this.desc.desc_cb.DESC_DO_VLD <= 0;
      this.desc.desc_cb.DESC_EMPTY  <= ~0;
      
    endfunction: new          
    
    // -- Enable Descriptor Manager -------------------------------------------
    // Enable Descriptor Manager and runs Descriptor Manager process
    task setEnabled();
      enabled = 1; // Descriptor Manager Enabling
      fork         
        run();      // Creating manager subprocess
        setEmpty(); // Creating subprocess for setting EMPTY signal
      join_none;    // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Descriptor Manager ------------------------------------------
    // Disable Descriptor Manager
    task setDisabled();
      enabled = 0; // Descriptor Manager Disabling
      desc.desc_cb.DESC_EMPTY <= 1;
    endtask : setDisabled
  
    // -- Add Descriptor ------------------------------------------------------
    // Adds descriptor do queue
    task addDescriptor(int flow, tDescriptor des);
      logic [63:0] data = 0;
      logic [127:0] descriptor = {des.address, des.flags, des.length};

      for (int i=0; i<2; i++)
      begin
        for (int j=0; j<64; j++)
          data[j] = descriptor[i*64+j];
        descQue[flow].push_back(data);
      end
    endtask : addDescriptor  
    
    // -- Run Descriptor Manager ----------------------------------------------
    // Take descriptor from queue and generate them to interface
    task run();
      int flow;

      while (enabled) begin            // Repeat while enabled        
        assert(randomize());           // Randomize rand variables
        // Wait for read
        waitForDescRead();
        // Send Descriptor
        flow = desc.desc_cb.DESC_ADDR;
        sendDescriptor(descQue[flow].pop_front());
      end
    endtask : run
        
    // -- Set Empty -----------------------------------------------------------
    // Sets EMPTY signal
    task setEmpty();
      logic [pFlows-1:0] isEmpty = 0;

      while (enabled) begin
        for (int i=0; i<pFlows; i++)
          if (!descQue[i].size()) isEmpty[i]= 1;
          else isEmpty[i] = 0;

        desc.desc_cb.DESC_EMPTY <= isEmpty;
        @(desc.desc_cb);
      end  
    endtask : setEmpty
    
    // -- Send Descriptor -----------------------------------------------------
    // Sets DESC_DO and wait until DESC_READ
    task sendDescriptor(logic [63:0] data);
      desc.desc_cb.DESC_DO     <= data;
      randomDoVldWait();
      desc.desc_cb.DESC_DO_VLD <= 1;
      @(desc.desc_cb);
      desc.desc_cb.DESC_DO_VLD <= 0;
    endtask : sendDescriptor
    
    // -- Wait For Desc Read --------------------------------------------------
    // Waits until DESC_READ
    task waitForDescRead();
      while (!desc.desc_cb.DESC_READ) 
        @(desc.desc_cb);
    endtask : waitForDescRead

    // -- Random wait ---------------------------------------------------------
    // Random wait during sending descriptor
    task randomDoVldWait();
      if (enDelay)
        repeat (delay)
          @(desc.desc_cb);
    endtask : randomDoVldWait
    
endclass : TxDescManager
