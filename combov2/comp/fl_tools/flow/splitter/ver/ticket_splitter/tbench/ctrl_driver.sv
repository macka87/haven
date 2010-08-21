/*
 * ctrl_driver.sv: Control interface (handshake) driver
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
 * $Id: ctrl_driver.sv 10588 2009-08-21 09:02:15Z xsanta06 $
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  // -- Control Interface Driver
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to FrameLink
   * interface. Transactions are received by 'transMbx'(Mailbox) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. You can send your custom
   * transaction by calling "sendTransaction" function.
   */
  class ControlDriver #(int pDataSize=1);
    
    // -- Private Class Atributes --
    string    inst;                          // Driver identification
    bit       enabled;                       // Driver is enabled
    bit       busy;                          // Driver is sending transaction
    tTransMbx transMbx;                      // Transaction mailbox
    DriverCbs cbs[$];                        // Callbacks list
    virtual iControl.in_tb #(pDataSize) ctrl;
    
    // ----
    rand bit enValidDelay;   // Enable/Disable valid delay
      // Enable/Disable valid delay (weights)
      int validDelayEn_wt             = 0; 
      int validDelayDisable_wt        = 3;

    rand int validDelay; // Valid delay
      // Valid delay
      int validDelayLow          = 0;
      int validDelayHigh         = 3;
    // ----

    // -- Constrains --
    constraint cDelays {
      enValidDelay dist { 1'b1 := validDelayEn_wt,
                          1'b0 := validDelayDisable_wt
                        };

      validDelay inside {
                         [validDelayLow:validDelayHigh]
                        };
    };


    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   tTransMbx transMbx, 
                   virtual iControl.in_tb #(pDataSize) ctrl
                   );
      this.enabled     = 0;           // Monitor is disabled by default     
      this.busy        = 0;           // Driver is not busy by default   
      this.ctrl        = ctrl;        // Store pointer Control interface 
      this.transMbx    = transMbx;    // Store pointer to mailbox
      this.inst        = inst;        // Store mark generator identifier
      
      this.ctrl.in_cb.CTRL_DATA_IN      <= 0;
      this.ctrl.in_cb.CTRL_DATA_IN_VLD  <= 0;
    endfunction

    // -- Set Callbacks -------------------------------------------------------
    // Put callback object into List 
    function void setCallbacks(DriverCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks
    
    // -- Enable Driver -------------------------------------------------------
    // Enable driver and runs driver process
    task setEnabled();
      enabled = 1; // Driver Enabling
      fork         
        run();          // Creating driver subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
 
    // -- Disable Driver ------------------------------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0; // Disable driver, after sending last transaction it ends
    endtask : setDisabled
    
    // -- Run Driver ----------------------------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
      ControlTransaction transaction;
      Transaction to;
            
      @(ctrl.in_cb);                   // Wait for clock
      
      while (enabled) begin            // Repeat while enabled
        assert(randomize());           // Randomize rand variables
        transMbx.get(to);              // Get transaction from mailbox 
        $cast(transaction,to);               
        sendTransaction(transaction);  // Send Transaction
//        transaction.display(inst);
      end
    endtask : run

    // -- Send Transaction ----------------------------------------------------
    // Send transaction to Frame Link interface
    task sendTransaction( ControlTransaction transaction );
      Transaction tr;
      $cast(tr, transaction); 
      
      // Driver is sending transaction
      busy = 1;

      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(tr, inst);       
      
      // Send transaction
      sendData(transaction);
    
      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(tr, inst);
      
      // Driver is not sending transaction
      busy = 0;
    endtask : sendTransaction

    // -- Send Data -----------------------------------------------------------
    // Send transaction data
    task sendData(ControlTransaction transaction);
      bit [pDataSize-1:0] aux;

      // Send data
      for (int i=0; i<pDataSize; i++)
        aux[i] = transaction.data[i];
      ctrl.in_cb.CTRL_DATA_IN     <= aux;

      // Insert valid delay
      insertValidDelay();
      ctrl.in_cb.CTRL_DATA_IN_VLD <= 1; 
      @(ctrl.in_cb);

      // Wait for data request
      waitForCtrlDataInRq();
      ctrl.in_cb.CTRL_DATA_IN_VLD <= 0; 
    endtask : sendData

    // -- Wait for ticket request --------------------------------------------
    // Waits for CRTL_DATA_IN_RQ signal
    task waitForCtrlDataInRq();
      while (!ctrl.in_cb.CTRL_DATA_IN_RQ) @(ctrl.in_cb);
    endtask : waitForCtrlDataInRq

    // ------------------------------------------------------------------------
    //! Insert Valid Delay
    /*!
     * Set random DATA_IN_VLD signal
     */
    task insertValidDelay();
      if (enValidDelay)
        repeat (validDelay) begin
          ctrl.in_cb.CTRL_DATA_IN_VLD <= 0; 
          @(ctrl.in_cb);
        end
    endtask: insertValidDelay

endclass : ControlDriver
