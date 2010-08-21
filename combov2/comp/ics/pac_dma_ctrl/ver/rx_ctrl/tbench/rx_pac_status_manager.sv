/*
 * rx_pac_status_manager.sv: Status Update manager for RX DMA Controller
 * Copyright (C) 2009 CESNET
 * Author(s): Marcela Šimková <xsimko03@stud.fit.vutbr.cz>
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
 * $Id: rx_pac_status_manager.sv 9322 2009-07-10 13:27:44Z xsimko03 $
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  // -- Status Update Manager Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to STATUS_UPDATE
   * interface and releasing data form RAM. Unit must be enabled by 
   * "setEnable()" function call. Generation can be stoped by "setDisable()" 
   * function call. 
   */
  class RxStatusManager #(pFlows = 2, pNumFlags = 8);
    
    // -----------------------------
    // -- Private Class Atributes --
    // -----------------------------
    string  inst;                               // Modul identification
    bit  enabled;                               // Modul is enabled
    logic[pNumFlags+16-1:0]  statusQueue[][$];  // Status Update Manager Queues
            
    // Status Update Manager interface    
    virtual iPacDmaCtrl.statrx_tb #(pFlows) stat;
    
    // delay to set HFULL for this inst
    rand int delaySetHfull;   
      int delaySetHfullLow             = 1000; 
      int delaySetHfullHigh            = 1500;
    
    // how long is HFULL set  
    rand int insideDelaySetHfull; 
      int insideDelaySetHfullLow       = 100;
      int insideDelaySetHfullHigh      = 500;  
      
    constraint cDelays {
      delaySetHfull inside {
                         [delaySetHfullLow:delaySetHfullHigh]
                        };

      insideDelaySetHfull inside {
                         [insideDelaySetHfullLow:insideDelaySetHfullHigh]
                        };               
    }
    
    // -------------------
    // -- Class Methods --
    // -------------------
    
    // -- Constructor ---------------------------------------------------------
    // Create Descriptor Manager object 
    function new ( string inst, 
                   virtual iPacDmaCtrl.statrx_tb #(pFlows) stat
                   );
            
      this.enabled     = 0;            // Modul is disabled by default
      this.inst        = inst;         // Store Modul identifier
      this.stat        = stat;         // Store pointer interface 
      
      statusQueue =new[pFlows];        // Status Queues store info from Status Up Manager for each interface
      stat.statrx_cb.SU_HFULL    <= 0;
    endfunction: new          
    
    // -- Enable Status Update Manager -------------------------------------------
    // Enable Status Update Manager and runs Status Update Manager process
    task setEnabled();
      enabled = 1;            // Status Update Enabling
      fork         
        run();                // Creating Modul subprocess
        setHfull();           // Creating subprocess for setting HFULL signal
      join_none;              // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Status Update Manager ------------------------------------------
    // Disable Status Update Manager
    task setDisabled();
      enabled = 0; // Status Update Manager Disabling
    endtask : setDisabled
  
    // -- Run Status Update Manager ----------------------------------------------
    task run();
      while (enabled) begin           // Repeat while enabled   
        waitForSuDataVld();           // Waiting for SU_DATA_VLD
        storeSUData();
      end
    endtask : run
    
    // -- Wait For Desc Read --------------------------------------------------
    // Waits until DESC_READ
    task waitForSuDataVld();
      while (!stat.statrx_cb.SU_DATA_VLD) 
        @(stat.statrx_cb);
    endtask : waitForSuDataVld
    
    //-- Store SU data ---------------------------------------------------------
    // Store SU data to statusQueue for each interface
    task storeSUData();
      int flow;
      logic[pNumFlags+16-1:0] flags_length;
    
      flow = stat.statrx_cb.SU_ADDR;
      flags_length = stat.statrx_cb.SU_DATA_RX;
      statusQueue[flow].push_back(flags_length);
      //$write("STATUS MAN: flags+length:  %x\n",flags_length);
      @(stat.statrx_cb); 
    endtask : storeSUData
    
    // -- Detect State of Queue ------------------------------------------------
    // Detect if the Queue is empty or not
    function int detectState(int flow);
      if ((statusQueue[flow].size())>0) return 1;  
      else return 0;
    endfunction : detectState
    
    // -- Set HFULL signal -----------------------------------------------------
    // Set HFULL signal - interface will be stoped
    task setHfull();
      while (enabled) begin
        assert(randomize());           // Randomize rand variables
        
        for (int i=0; i<pFlows; i++)begin
          repeat (delaySetHfull) @(stat.statrx_cb);
          stat.statrx_cb.SU_HFULL[i]    <= 1;
          repeat (insideDelaySetHfull) @(stat.statrx_cb);
          stat.statrx_cb.SU_HFULL    <= 0;
        end  
      end
    endtask : setHfull
    
  endclass : RxStatusManager  