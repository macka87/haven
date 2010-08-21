/*
 * su_driver.sv: Driver for Status Update interface
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
 * $Id: su_driver.sv 11736 2009-10-25 11:01:35Z xsanta06 $
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  // -- Status Update Driver
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to Status Update 
   * interface. Transactions are received by 'transMbx'(Mailbox) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. You can send your custom
   * transaction by calling "sendUpdate" function.
   */
  class SuDriver #(int pFlows = 2, int pDataSize = 4);
    
    // -----------------------------
    // -- Private Class Atributes --
    // -----------------------------
    string    inst;                          // Driver identification
    bit       enabled;                       // Driver is enabled
    bit       busy;                          // Driver is sending transaction
    tTransMbx transMbx;                      // Transaction mailbox
    DriverCbs cbs[$];                        // Callbacks list
    virtual iSu.su_tb #(pFlows, pDataSize) su;

    // ----
    rand bit enDelay;   // Enable/Disable DATA_VLD delay
      // Enable/Disable DATA_VLD delay (weights)
      int delayEn_wt             = 10; 
      int delayDisable_wt        = 0;

    rand int delay; // DATA_VLD delay
      // DATA_VLD delay limits
      int delayLow          = 8;
      int delayHigh         = 192;
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
    // Create Status Update Driver object 
    function new ( string inst, 
                   tTransMbx transMbx, 
                   virtual iSu.su_tb #(pFlows, pDataSize) su
                   );      
      this.enabled     = 0;            // Driver is disabled by default
      this.inst        = inst;         // Store driver identifier
      this.transMbx    = transMbx;     // Store pointer to mailbox
      this.su          = su;           // Store pointer interface 
      
      this.su.su_cb.SU_ADDR     <= 0;
      this.su.su_cb.SU_DATA     <= 0;
      this.su.su_cb.SU_DVLD <= 0;
      
    endfunction: new          
    
    // -- Set Callbacks -------------------------------------------------------
    // Put callback object into List 
    function void setCallbacks(DriverCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks
    
    // -- Enable Driver -------------------------------------------------------
    // Enable Driver and run Driver process
    task setEnabled();
      enabled = 1; // Driver Enabling
      fork         
        run();      // Creating driver subprocess
      join_none;    // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Driver ------------------------------------------------------
    // Disable Driver
    task setDisabled();
      enabled = 0; // Driver Disabling
    endtask : setDisabled
  
    // -- Run Driver ----------------------------------------------------------
    // Create status updates and generate them to interface
    task run();
      StatusUpdateTransaction transaction;
      Transaction to;
            
      while (enabled) begin            // Repeat while enabled
        // Randomize rand variables
        assert(randomize());           

        // Get transaction from mailbox 
        transMbx.get(to);              
        $cast(transaction,to);               

        // Driver is sending transaction
        busy = 1;

        // Call transaction preprocesing, if is available
        foreach (cbs[i]) cbs[i].pre_tx(to, inst);       
      
        // Wait for not HFULL
        waitForNotHFull(transaction.address);

        // Send update
        sendUpdate(transaction);
//        transaction.display("SU Driver");
    
        // Call transaction postprocesing, if is available
        foreach (cbs[i]) cbs[i].post_tx(to, inst);
      
        // Driver is not sending transaction
        busy = 0;
      end
    endtask : run
        
    // -- Send Update ---------------------------------------------------------
    // Sets SU_DATA and SU_ADDR
    task sendUpdate(StatusUpdateTransaction tr);
      for (int i=0; i<tr.data.size; i++)
        su.su_cb.SU_DATA[i] <= tr.data[i];
      su.su_cb.SU_ADDR     <= tr.address;
      // Random wait
      randomDataVldWait();
      // Send valid
      su.su_cb.SU_DVLD <= 1;
      @(su.su_cb);
      su.su_cb.SU_DVLD <= 0;
    endtask : sendUpdate

    // -- Random wait ---------------------------------------------------------
    // Random wait during sending update
    task randomDataVldWait();
      if (enDelay)
        repeat (delay)
          @(su.su_cb);
    endtask : randomDataVldWait
    
    // -- Wait For Not HFull --------------------------------------------------
    // Wait until HFULL signal is active
    task waitForNotHFull(int address);
      while (su.su_cb.SU_HFULL[address] == 1)
        @(su.su_cb);
    endtask : waitForNotHFull
    
endclass : SuDriver
