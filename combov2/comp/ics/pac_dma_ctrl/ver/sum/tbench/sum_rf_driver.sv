/*
 * sum_rf_driver.sv: Driver for Status Update Manager RX_RF interface
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
 * $Id: sum_rf_driver.sv 11736 2009-10-25 11:01:35Z xsanta06 $
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  // -- SUM RX_RF Driver Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to SUM RX_RF
   * interface. Transactions are received by 'transMbx'(Mailbox) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. You can send your custom
   * transaction by calling "sendTransaction" function.
   */
  class SumRfDriver #(int pFlows=4, int pBlockSize=4);

    // -- Private Class Atributes --
    string    inst;                          // Driver identification
    bit       enabled;                       // Driver is enabled
    bit       busy;                          // Driver is sending transaction
    tTransMbx transMbx;                      // Transaction mailbox
    DriverCbs cbs[$];                        // Callbacks list
    virtual iSum.reqFifo_tb #(pFlows,pBlockSize) rf;
  
    // ----
    rand bit enDelay;   // Enable/Disable delays between transactions
      // Enable/Disable delays between transaction (weights)
      int delayEn_wt             = 1; 
      int delayDisable_wt        = 3;

    rand int delay; // Delay between transactions
      // Delay between transactions limits
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
    
    
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create driver object 
    function new ( string inst, 
                   tTransMbx transMbx, 
                   virtual iSum.reqFifo_tb #(pFlows,pBlockSize) rf
                         );
      this.enabled     = 0;            // Driver is disabled by default
      this.busy        = 0;            // Driver is not busy by default   
      this.rf          = rf;           // Store pointer interface 
      this.transMbx    = transMbx;     // Store pointer to mailbox
      this.inst        = inst;         // Store driver identifier

      this.rf.reqFifo_cb.RX_RF_DOUT      <= 0;
      this.rf.reqFifo_cb.RX_RF_DVLD      <= 0;
      this.rf.reqFifo_cb.RX_RF_EMPTY     <= 0;
      this.rf.reqFifo_cb.RX_RF_STATUS    <= 0;
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
    // Send transaction to Request Fifo interface
    task sendTransaction( SumRfTransaction transaction );
      Transaction tr;
      $cast(tr, transaction); 
      
      // Driver is sending transaction
      busy = 1;

      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(tr, inst);       
      
      // Wait for read request
      waitForRfRead();

      // Wait before sending transaction
      if (enDelay) repeat (delay) @(rf.reqFifo_cb);
            
      // Send transaction
      sendData(transaction);
      
      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(tr, inst);
      
      // Driver is not sending transaction
      busy = 0;
    endtask : sendTransaction
    
    // -- Private Class Methods --
    
    // -- Run Driver ----------------------------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
      SumRfTransaction transaction;
      Transaction to;
            
      @(rf.reqFifo_cb);                        // Wait for clock
      
      while (enabled) begin            // Repeat while enabled
        assert(randomize());           // Randomize rand variables
        transMbx.get(to);              // Get transaction from mailbox 
        $cast(transaction,to);               
        sendTransaction(transaction);  // Send Transaction
//        transaction.display(inst);
      end
    endtask : run
    

    // -- Wait for RF Read ----------------------------------------------------
    // Wait for read request for next data
    task waitForRfRead();
      while (rf.reqFifo_cb.RX_RF_READ == 0) begin
        @(rf.reqFifo_cb);
      end
    endtask : waitForRfRead
        
    // -- Random wait ---------------------------------------------------------
    // Random wait during sending transaction (Set SRC_RDY_N to 1)
    task randomWait();
//      if (enInsideTxDelay)
//        repeat (insideTxDelay) begin
//          fl.cb.SRC_RDY_N <= 1;
//          @(fl.cb); // Wait for send
//        end
//      fl.cb.SRC_RDY_N <= 0;
//      assert(randomize());     // Randomize variables for next randomWait
    endtask : randomWait
       

    // -- Send transaction data -----------------------------------------------
    // Send transaction data
    task sendData(inout SumRfTransaction tr);
      logic[63:0] address = tr.descStartAddr;

//      $write("descStartAddr:%0x\n",tr.descStartAddr);
      tr.rfRAddr = rf.reqFifo_cb.RX_RF_RADDR;
      rf.reqFifo_cb.RX_RF_DOUT <= {tr.blockLength, address};
      rf.reqFifo_cb.RX_RF_DVLD <= 1;
      @(rf.reqFifo_cb);
      rf.reqFifo_cb.RX_RF_DVLD <= 0;
    endtask : sendData
     
  endclass : SumRfDriver 

