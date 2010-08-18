/*
 * fl_driver.sv: FrameLink Driver
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
 * $Id: fl_driver.sv 10094 2009-08-05 12:55:47Z xsanta06 $
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  // -- Frame Link Driver Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to FrameLink
   * interface. Transactions are received by 'transMbx'(Mailbox) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. You can send your custom
   * transaction by calling "sendTransaction" function.
   */
  class FrameLinkDriver #(int pDataWidth=32, int pDremWidth=2);

    // -- Private Class Atributes --
    string    inst;                          // Driver identification
    bit       enabled;                       // Driver is enabled
    bit       busy;                          // Driver is sending transaction
    tTransMbx transMbx;                      // Transaction mailbox
    DriverCbs cbs[$];                        // Callbacks list
    virtual iFrameLinkRx.tb #(pDataWidth,pDremWidth) fl;
  
    // ----
    rand bit enTxDelay;   // Enable/Disable delays between transactions
      // Enable/Disable delays between transaction (weights)
      int txDelayEn_wt             = 1; 
      int txDelayDisable_wt        = 3;

    rand int txDelay; // Delay between transactions
      // Delay between transactions limits
      int txDelayLow          = 0;
      int txDelayHigh         = 3;
    // ----

    // ----
    rand bit enInsideTxDelay;     // Enable/Disable delays inside transaction
      // Enable/Disable delays inside transaction weights
      int insideTxDelayEn_wt       = 1; 
      int insideTxDelayDisable_wt  = 3;
      
    rand int insideTxDelay;  
      // Minimal/Maximal delay between transaction words
      int insideTxDelayLow         = 0;
      int insideTxDelayHigh        = 3;
    // ----
    
    // -- Constrains --
    constraint cDelays {
      enTxDelay dist { 1'b1 := txDelayEn_wt,
                       1'b0 := txDelayDisable_wt
                     };

      txDelay inside {
                      [txDelayLow:txDelayHigh]
                     };

      enInsideTxDelay dist { 1'b1 := insideTxDelayEn_wt,
                             1'b0 := insideTxDelayDisable_wt
                     };
                     
      insideTxDelay inside {
                            [txDelayLow:txDelayHigh]
                     };               
      }
    
    
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create driver object 
    function new ( string inst, 
                   tTransMbx transMbx, 
                   virtual iFrameLinkRx.tb #(pDataWidth,pDremWidth) fl
                         );
      this.enabled     = 0;            // Driver is disabled by default
      this.busy        = 0;            // Driver is not busy by default   
      this.fl          = fl;           // Store pointer interface 
      this.transMbx    = transMbx;     // Store pointer to mailbox
      this.inst        = inst;         // Store driver identifier

      this.fl.cb.DATA      <= 0;
      this.fl.cb.DREM      <= 0;
      this.fl.cb.SOF_N     <= 1;
      this.fl.cb.EOF_N     <= 1;
      this.fl.cb.SOP_N     <= 1;
      this.fl.cb.EOP_N     <= 1;
      this.fl.cb.SRC_RDY_N <= 1;
    endfunction: new  
    
    
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
        run();     // Creating driver subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Driver ------------------------------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0; // Disable driver, after sending last transaction it ends
    endtask : setDisabled
    
    // -- Send Transaction ----------------------------------------------------
    // Send transaction to Frame Link interface
    task sendTransaction( FrameLinkTransaction transaction );
      Transaction tr;
      $cast(tr, transaction); 
      
      // Driver is sending transaction
      busy = 1;

      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(tr, inst);       
      
      // Wait before sending transaction
      if (enTxDelay) repeat (txDelay) @(fl.cb);
            
      // Send transaction
      sendData(transaction);
      
      // Set not ready 
      fl.cb.SRC_RDY_N <= 1;
    
      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(tr, inst);
      
      // Driver is not sending transaction
      busy = 0;
    endtask : sendTransaction
    
    // -- Private Class Methods --
    
    // -- Run Driver ----------------------------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
      FrameLinkTransaction transaction;
      Transaction to;
            
      @(fl.cb);                        // Wait for clock
      
      while (enabled) begin            // Repeat while enabled
        assert(randomize());           // Randomize rand variables
        transMbx.get(to);              // Get transaction from mailbox 
        $cast(transaction,to);               
        sendTransaction(transaction);  // Send Transaction
//        transaction.display(inst);
      end
    endtask : run
    

    // -- Wait for accept -----------------------------------------------------
    // Wait for accepting of general bits word of transaction
    task waitForAccept();
      while (fl.cb.DST_RDY_N) begin
        @(fl.cb);
      end;
    endtask : waitForAccept
        
    // -- Random wait ---------------------------------------------------------
    // Random wait during sending transaction (Set SRC_RDY_N to 1)
    task randomWait();
      if (enInsideTxDelay)
        repeat (insideTxDelay) begin
          fl.cb.SRC_RDY_N <= 1;
          @(fl.cb); // Wait for send
        end
      fl.cb.SRC_RDY_N <= 0;
      assert(randomize());     // Randomize variables for next randomWait
    endtask : randomWait
       

    // -- Send transaction data -----------------------------------------------
    // Send transaction data
    task sendData(FrameLinkTransaction tr);
      int m = 0;
      logic[pDataWidth-1:0] dataToSend = 0;
      
      // -- For all packets --
      for (int i=0; i < tr.packetCount; i++) begin              
        
        // -- For all bytes in packet --
        for (int j=0; j < tr.data[i].size; j++) begin 
 
          // -- Set SOP a SOF
          if (j<pDataWidth/8) begin
            fl.cb.SOP_N <= 0;                      //Set Start of Packet
            if (i==0) fl.cb.SOF_N <=0;             //Set Start of Frame
          end

          // Set one Data Byte
          for (int k=0; k < 8; k++) 
            dataToSend[m++] = tr.data[i][j][k];
                  

          // Last Byte in Packet
          if (j==tr.data[i].size-1) begin          //Last byte of packet
            fl.cb.EOP_N<=0;                             //Set End Of Packet
            if (i==tr.packetCount-1)                //Last byte of Frame
              fl.cb.EOF_N<=0;                           //Set End of Frame

            // Set REM signal
            if (tr.data[i].size%(pDataWidth/8) == 0)
              fl.cb.DREM <= (pDataWidth/8)-1;
            else
              fl.cb.DREM <= (tr.data[i].size%(pDataWidth/8))-1;

            m=pDataWidth;
          end

          // When data word is ready to send
          if (m==pDataWidth) begin
            fl.cb.DATA <= dataToSend;
            randomWait();     // Create not ready
            @(fl.cb);         // Send data
            waitForAccept();  // Wait until oposit side set ready

            // Init for sending next data word
            fl.cb.SOF_N<=1;       
            fl.cb.SOP_N<=1;
            fl.cb.EOP_N<=1;
            fl.cb.EOF_N<=1;
            dataToSend = 0;
            m=0;
          end

        end
      end

    endtask : sendData
     
  endclass : FrameLinkDriver 

