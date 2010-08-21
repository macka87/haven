/*
 * au_driver.sv: Align Unit Driver
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
 * $Id: au_driver.sv 3590 2008-07-16 09:05:59Z xsanta06 $
 *
 * TODO:
 *
 */
   
//   typedef struct {
//     int dstAddr;
//     int dataLen;
//   }tTransInfo;
   import sv_au_pkg::*;
  // --------------------------------------------------------------------------
  // -- Align Unit Driver Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to Align Unit
   * interface. Transactions are received by 'transMbx'(Mailbox) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. You can send your custom
   * transaction by calling "sendTransaction" function.
   */
  class AlignUnitDriver;

    // -- Private Class Atributes --
    string    inst;                             // Driver identification
    bit       enabled;                          // Driver is enabled
    tTransMbx transMbx;                         // Transaction mailbox
    DriverCbs cbs[$];                           // Callbacks list
    virtual iAlignUnit.rx_tb rx;
    tInfoQue tr_info;                           // List with transaction info
  
    // ----
    rand bit enRxDelay;   // Enable/Disable delays between transactions
      // Enable/Disable delays between transaction (weights)
      int rxDelayEn_wt             = 1; 
      int rxDelayDisable_wt        = 3;

    rand integer rxDelay; // Delay between transactions
      // Delay between transactions limits
      int rxDelayLow          = 0;
      int rxDelayHigh         = 3;
    // ----

    // ----
    rand bit enInsideRxDelay;     // Enable/Disable delays inside transaction
      // Enable/Disable delays inside transaction weights
      int insideRxDelayEn_wt       = 1; 
      int insideRxDelayDisable_wt  = 3;
      // Minimal/Maximal delay between transaction words
      int insideRxDelayLow         = 0;
      int insideRxDelayHigh        = 3;
    // ----
    
    // ----
    rand int src_addr;   // Source address
    rand int dst_addr;   // Destination address
    
    // -- Constrains --
    constraint cDelays {
      enRxDelay dist { 1'b1 := rxDelayEn_wt,
                       1'b0 := rxDelayDisable_wt
                     };

      rxDelay inside {
                      [rxDelayLow:rxDelayHigh]
                     };

      enInsideRxDelay dist { 1'b1 := insideRxDelayEn_wt,
                             1'b0 := insideRxDelayDisable_wt
                     };
      
      src_addr inside {
                       [0:7]
                      };
                          
      dst_addr inside {
                       [0:7]
                      };
      }
    
    
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create driver object 
    function new ( string inst, 
                   tTransMbx transMbx, 
                   virtual iAlignUnit.rx_tb rx,
                   tInfoQue tr_info
                         );
      this.enabled     = 0;            // Driver is disabled by default
      this.rx          = rx;           // Store pointer interface 
      this.transMbx    = transMbx;     // Store pointer to mailbox
      this.inst        = inst;         // Store driver identifier
      this.tr_info     = tr_info;

      this.rx.rx_cb.IN_DATA      <= 0;
      this.rx.rx_cb.IN_SOF       <= 0;
      this.rx.rx_cb.IN_EOF       <= 0;
      this.rx.rx_cb.IN_SRC_RDY   <= 0;
      this.rx.rx_cb.DATA_LEN     <= 0;
      this.rx.rx_cb.SRC_ADDR     <= 0;
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
    task sendTransaction( AlignUnitTransaction transaction );
      Transaction tr;
      $cast(tr, transaction);
      
      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(tr, inst);

      // Wait before sending transaction
      if (enRxDelay) repeat (rxDelay) @(rx.rx_cb);
      
      // Send transaction
      sendData(transaction);
      
      // Set not ready 
      rx.rx_cb.IN_SOF     <= 0;
      rx.rx_cb.IN_EOF     <= 0;
      rx.rx_cb.IN_SRC_RDY <= 0;
    
      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(tr, inst);
    endtask : sendTransaction
    
    // -- Private Class Methods --
    
    // -- Run Driver ----------------------------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
      AlignUnitTransaction transaction;
      Transaction to;
      @(rx.rx_cb);                     // Wait for clock
      while (enabled) begin            // Repeat while enabled
        transMbx.get(to);              // Get transaction from mailbox
        $cast(transaction,to);
        assert(randomize());
        addInfo(transaction);
        sendTransaction(transaction);  // Send Transaction
//        transaction.display("Driver");
      end
    endtask : run
    

    // -- Wait for accept -----------------------------------------------------
    // Wait for accepting of general bits word of transaction
    task waitForAccept();
      while (!rx.rx_cb.IN_DST_RDY) begin
        @(rx.rx_cb);
      end;
    endtask : waitForAccept

    //-- Random intertransaction wait -----------------------------------------
    function integer getRandomWait();
       if (enInsideRxDelay)
         return $urandom_range(insideRxDelayLow, insideRxDelayHigh);
       else
         return 0;
    endfunction : getRandomWait
        
    // -- Random wait ---------------------------------------------------------
    // Random wait during sending transaction (Set SRC_RDY to 0)
    task randomWait();
      repeat (getRandomWait()) begin
        rx.rx_cb.IN_SRC_RDY <= 0;
        @(rx.rx_cb); // Wait for send
      end;
      rx.rx_cb.IN_SRC_RDY <= 1;
    endtask : randomWait
    
    // -- Add Info ------------------------------------------------------------
    // Add info about transaction
    task addInfo(AlignUnitTransaction tr);
      tTransInfo info;
      
      info.dstAddr = dst_addr;
      info.dataLen = tr.data.size%8;
      tr_info.put(info);
    endtask : addInfo
       

    // -- Send transaction data -----------------------------------------------
    // Send transaction data
    task sendData(AlignUnitTransaction tr);
      integer m = 0;
      logic[63:0] dataToSend = 0;

      // Align data from transaction to rx.rx_cb.DATA
      rx.rx_cb.IN_SOF       <= 1;               // Set Start of frame        
      rx.rx_cb.IN_SRC_RDY   <= 1;               // Source is ready to send data
      rx.rx_cb.IN_DATA      <= 0;               // Null the fl.DATA
      rx.rx_cb.DATA_LEN     <= tr.data.size%8;  // Send DATA_LEN
      rx.rx_cb.SRC_ADDR     <= src_addr;        // Send SRC_ADDR
      rx.rx_cb.DST_ADDR     <= dst_addr;        // Send SRC_ADDR

      for (int i=0; i<src_addr*8; i++)
        dataToSend[m++]=0;//$random;   // Make correct displacement of data in first word

      for (int i=0; i<tr.data.size; i++) 
      begin  
        for (int j=0; j < 8; j++)
          dataToSend[m++] = tr.data[i][j];  
          
        if (i==tr.data.size-1) rx.rx_cb.IN_EOF <= 1;    // Last word - set EOF
        else rx.rx_cb.IN_EOF <= 0;
        
        // When is data ready to send
        if (m==64 || i==tr.data.size-1) begin
          rx.rx_cb.IN_DATA <= dataToSend;
//          randomWait();            // Create not ready
          @(rx.rx_cb);             // Send data
          waitForAccept();         // Wait until oposit side set ready
          rx.rx_cb.IN_DATA <=0;    // Null the fl.DATA
          rx.rx_cb.IN_SOF  <=0;
          dataToSend = 0;
          m=0;                     // Init constant for sending next word
        end
      end

    endtask : sendData
     
  endclass : AlignUnitDriver 

