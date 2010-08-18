//
// ib_driver_pkg.sv: Internal Bus Driver
// Copyright (C) 2007 CESNET
// Author(s): Petr Kobierský <kobiersky@liberouter.org>
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in
//    the documentation and/or other materials provided with the
//    distribution.
// 3. Neither the name of the Company nor the names of its contributors
//    may be used to endorse or promote products derived from this
//    software without specific prior written permission.
//
// This software is provided ``as is'', and any express or implied
// warranties, including, but not limited to, the implied warranties of
// merchantability and fitness for a particular purpose are disclaimed.
// In no event shall the company or contributors be liable for any
// direct, indirect, incidental, special, exemplary, or consequential
// damages (including, but not limited to, procurement of substitute
// goods or services; loss of use, data, or profits; or business
// interruption) however caused and on any theory of liability, whether
// in contract, strict liability, or tort (including negligence or
// otherwise) arising in any way out of the use of this software, even
// if advised of the possibility of such damage.
//
// $Id: ib_driver.sv 3980 2008-07-24 18:26:33Z xkobie00 $
//

  // --------------------------------------------------------------------------
  // -- Internal Bus Driver Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to Internal Bus
   * interface. Transactions are received by 'transMbx'(Mailbox) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. You can send your custom
   * transcaction by calling "sendTransaction" function.
   */
  class InternalBusDriver#(int pDataWidth=64);
  
    // -- Private Class Atributes --
    string    inst;                                             // Driver identification
    bit       enabled;                                          // Driver is enabled
    tTransMbx transMbx;                                         // Transaction mailbox
    DriverCbs cbs[$];                                           // Callbacks list
    virtual   iInternalBusRx.driver #(pDataWidth) internalBus;  // Internal Bus interface
 
    // ----
    rand bit enTxDelay;   // Enable/Disable delays between transactions
      // Enable/Disable delays between transaction (weights)
      int txDelayEn_wt             = 0; 
      int txDelayDisable_wt        = 1;

    rand integer txDelay; // Delay between transactions
      // Delay between transactions limits
      int txDelayLow          = 0;
      int txDelayHigh         = 3;
    // ----

    // ----
    rand bit enInsideTxDelay;     // Enable/Disable delays inside transaction
      // Enable/Disable delays inside transaction weights
      int insideTxDelayEn_wt       = 0;
      int insideTxDelayDisable_wt  = 1;
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
      }


    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create driver object 
    function new ( string inst,
                   tTransMbx transMbx,
                   virtual iInternalBusRx.driver #(pDataWidth)  internalBus
                 );
      this.inst        = inst;         // Store driver identifier
      this.enabled     = 0;            // Driver is disabled by default
      this.internalBus = internalBus;  // Store pointer interface 
      this.transMbx    = transMbx;     // Store pointer to mailbox   
      // Setting default values for Internal Bus interface
      this.internalBus.cb_driver.DATA      <= 64'h0000000000000000;
      this.internalBus.cb_driver.SOP_N     <= 1;
      this.internalBus.cb_driver.EOP_N     <= 1;
      this.internalBus.cb_driver.SRC_RDY_N <= 1;
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
    // Send transaction to Internal Bus interface
    task sendTransaction(InternalBusTransaction transaction);
      Transaction tr;
      $cast(tr, transaction);

      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(tr, inst);                 
 
      // Wait before sending transaction
      if (enTxDelay) repeat (txDelay) @(internalBus.cb_driver);

      // Send transaction
      case (transaction.transType)
        L2LW:
          sendL2LW(transaction);
        L2LR:
          sendL2LR(transaction);
        L2GW:
          sendL2GW(transaction);
        G2LR:
          sendG2LR(transaction);
        RDC:
          sendRDC(transaction);
        RDCL:
          sendRDCL(transaction);
      endcase;

      // Set not ready 
      internalBus.cb_driver.SOP_N     <= 1;
      internalBus.cb_driver.EOP_N     <= 1;
      internalBus.cb_driver.SRC_RDY_N <= 1;
       
      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(tr, inst);

    endtask : sendTransaction

    // -- Private Class Methods --
    
    // -- Run Driver ----------------------------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
      InternalBusTransaction transaction;
      Transaction to;
      @(internalBus.cb_driver);        // Wait for clock
      while (enabled) begin            // Repeat while enabled
        transMbx.get(to);              // Get transaction from mailbox
        $cast(transaction,to);         // Casting
        assert(randomize());           // Delay randomization
        sendTransaction(transaction);  // Send Transaction
      end
    endtask : run
    
    // -- Wait for accept -----------------------------------------------------
    // Wait for accepting of 64 bits word of transaction
    task waitForAccept();
      while (internalBus.cb_driver.DST_RDY_N) begin
        @(internalBus.cb_driver);
      end;
    endtask : waitForAccept

    //-- Random intertransaction wait -----------------------------------------
    function integer getRandomWait();
       if (enInsideTxDelay)
         return $urandom_range(insideTxDelayLow, insideTxDelayHigh);
       else
         return 0;
    endfunction : getRandomWait

    // -- Random wait ---------------------------------------------------------
    // Random wait during sending transaction (Set SRC_RDY_N to 1)
    task randomWait(InternalBusTransaction transaction);
      repeat (getRandomWait()) begin
        internalBus.cb_driver.SRC_RDY_N <= 1;
        @(internalBus.cb_driver); // Wait for send
      end;
        internalBus.cb_driver.SRC_RDY_N <= 0;
    endtask : randomWait

    // -- Send Header 0 -------------------------------------------------------
    // Send Header 0
    task sendHdr0(logic [63:0] hdr);
      // Send header 0
      internalBus.cb_driver.DATA      <= hdr;
      internalBus.cb_driver.SOP_N     <= 0;
      internalBus.cb_driver.EOP_N     <= 1;
      internalBus.cb_driver.SRC_RDY_N <= 0;
    endtask : sendHdr0

    // -- Send Header 1 -------------------------------------------------------
    // Send Header 1
    task sendHdr1(logic [63:0] hdr, bit eop_n);
      // Send header 0
      internalBus.cb_driver.DATA      <= hdr;
      internalBus.cb_driver.SOP_N     <= 1;
      internalBus.cb_driver.EOP_N     <= eop_n;
      internalBus.cb_driver.SRC_RDY_N <= 0;
    endtask : sendHdr1

    // -- Send transaction data -----------------------------------------------
    // Send transaction data
    task sendData(InternalBusTransaction tr, integer offset);
      logic data[];      // Data to write

      // Create bit array for saving write data
      data = new[(tr.data.size+offset)*8];
      // Clear part of bit array (data allign part)
      for (integer i = 0; i < offset*8; i++)
        data[i]=1'b0;
      // Allign data from transaction to bit array
      for (integer i=0; i < tr.data.size; i++)
        for (integer j=0; j < 8; j++)
          data[8*i+j+(offset*8)] = tr.data[i][j];
 
      // Send Data
      for (integer i=0; i < data.size; i=i+64) begin
        logic [63:0] write_data = 64'h0000000000000000;
        // Fill data variable
        for (integer j=0; j < 64; j++)
          if ((i+j) < data.size)
            write_data[j] = data[i+j];

        randomWait(tr);    // Random wait during transaction

        // Generate signals
        internalBus.cb_driver.DATA      <= write_data;
        internalBus.cb_driver.SOP_N     <= 1;
        internalBus.cb_driver.SRC_RDY_N <= 0;
        if ((i+64) >= data.size)
          internalBus.cb_driver.EOP_N   <= 0;
        else
          internalBus.cb_driver.EOP_N   <= 1;
  
        @(internalBus.cb_driver);
        waitForAccept();   // Wait for accept
       end
    endtask : sendData

    // -- Send L2LW -----------------------------------------------------------
    // Send L2LW transaction, data is aligned to destination adress
    task sendL2LW ( InternalBusTransaction tr);
      logic [63:0] hdr0; // Header data0
      logic [63:0] hdr1; // Header data1
          
      // Assembly headers
      hdr0 = {tr.localAddr,tr.tag, L2LW_TYPE, tr.length};
      hdr1 = {32'h00000000, tr.globalAddr[31:0]};
     
      randomWait(tr);           // Random wait during transaction
      sendHdr0(hdr0);           // Send header 0
      @(internalBus.cb_driver);
      waitForAccept();          // Wait for accept

      randomWait(tr);           // Random wait during transaction
      sendHdr1(hdr1, 1);        // Send header 1 without eop
      @(internalBus.cb_driver);
      waitForAccept();          // Wait for accept
           
      sendData(tr, tr.localAddr[2:0]); // Send Data
    endtask : sendL2LW

    // -- Send L2LR -----------------------------------------------------------
    // Send L2LR transaction, Read data from source address
    task sendL2LR( InternalBusTransaction tr );
      logic [63:0] hdr0; // Header data0
      logic [63:0] hdr1; // Header data1
      
      // Assembly headers
      hdr0 = {tr.localAddr,tr.tag, L2LR_TYPE, tr.length};
      hdr1 = {32'h00000000, tr.globalAddr[31:0]};
      
      randomWait(tr);           // Random wait during transaction
      sendHdr0(hdr0);           // Send header 0
      @(internalBus.cb_driver);
      waitForAccept();          // Wait for accept

      randomWait(tr);           // Random wait during transaction
      sendHdr1(hdr1, 0);        // Send header 1 without eop
      @(internalBus.cb_driver);
      waitForAccept();          // Wait for accept


    endtask : sendL2LR

    // -- Send L2GW -----------------------------------------------------------
    // Send L2GW transaction, Write data to global address space
    task sendL2GW( InternalBusTransaction tr );
      logic [63:0] hdr0; // Header data0
      logic [63:0] hdr1; // Header data1

      // Assembly headers
      hdr0 = {tr.globalAddr[31:0],tr.tag, L2GW_TYPE, tr.length};
      hdr1 = {tr.globalAddr[63:32], tr.localAddr};
      
      randomWait(tr);           // Random wait during transaction
      sendHdr0(hdr0);           // Send header 0
      @(internalBus.cb_driver);
      waitForAccept();          // Wait for accept


      randomWait(tr);           // Random wait during transaction
      sendHdr1(hdr1, 1);        // Send header 1 without eop
      @(internalBus.cb_driver);
      waitForAccept();          // Wait for accept


      sendData(tr, tr.globalAddr[2:0]); // Send Data
    endtask : sendL2GW

    // -- Send G2LR -----------------------------------------------------------
    // Send G2LR transaction, Read data from global address space
    task sendG2LR( InternalBusTransaction tr );
      logic [63:0] hdr0; // Header data0
      logic [63:0] hdr1; // Header data1

      // Assembly headers
      hdr0 = {tr.globalAddr[31:0],tr.tag, G2LR_TYPE, tr.length};
      hdr1 = {tr.globalAddr[63:32], tr.localAddr};
      
      randomWait(tr);           // Random wait during transaction
      sendHdr0(hdr0);           // Send header 0
      @(internalBus.cb_driver);
      waitForAccept();          // Wait for accept



      randomWait(tr);           // Random wait during transaction
      sendHdr1(hdr1, 0);        // Send header 1 without eop
      @(internalBus.cb_driver);
      waitForAccept();          // Wait for accept

    endtask : sendG2LR

    // -- Send RDC ------------------------------------------------------------
    // Send RDC transaction, Read completition transaction, data is alligned to
    // destination address (without last flag)
    task sendRDC( InternalBusTransaction tr );
      logic [63:0] hdr0; // Header data0
      logic [63:0] hdr1; // Header data1
       
      // Assembly headers
      hdr0 = {tr.globalAddr[31:0],tr.tag, RDC_TYPE, tr.length};
      hdr1 = {32'h00000000, tr.localAddr};
      
      randomWait(tr);           // Random wait during transaction
      sendHdr0(hdr0);           // Send header 0
      @(internalBus.cb_driver);
      waitForAccept();          // Wait for accept

      
      randomWait(tr);           // Random wait during transaction
      sendHdr1(hdr1, 1);        // Send header 1 without eop
      @(internalBus.cb_driver);
      waitForAccept();          // Wait for accept


      sendData(tr, tr.globalAddr[2:0]); // Send Data
    endtask : sendRDC

    // -- Send RDCL -----------------------------------------------------------
    // Send RDCL transaction, Read completition transakce, data is aligned to
    // destination addres (with last flag)
    task sendRDCL( InternalBusTransaction tr );
      logic [63:0] hdr0; // Header data0
      logic [63:0] hdr1; // Header data1

      // Assembly headers
      hdr0 = {tr.globalAddr[31:0],tr.tag, RDCL_TYPE, tr.length};
      hdr1 = {32'h00000000, tr.localAddr};
              

      randomWait(tr);           // Random wait during transaction
      sendHdr0(hdr0);           // Send header 0
      @(internalBus.cb_driver);
      waitForAccept();          // Wait for accept


      randomWait(tr);           // Random wait during transaction
      sendHdr1(hdr1, 1);        // Send header 1 without eop
      @(internalBus.cb_driver);
      waitForAccept();          // Wait for accept


      sendData(tr, tr.globalAddr[2:0]); // Send Data
    endtask : sendRDCL

  endclass : InternalBusDriver

