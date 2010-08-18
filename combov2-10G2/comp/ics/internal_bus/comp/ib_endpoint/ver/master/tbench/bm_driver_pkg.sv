/*
 * bm_driver_pkg.sv: Bus Master Driver
 * Copyright (C) 2007 CESNET
 * Author(s): Tomas Malek <tomalek@liberouter.org>
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
 * $Id: bm_driver_pkg.sv 333 2007-09-05 20:07:59Z xkobie00 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package bm_driver_pkg;

  import bm_transaction_pkg::*; // Transaction package

  // --------------------------------------------------------------------------
  // -- Bus Master Driver Callbacks
  // --------------------------------------------------------------------------
  class BmDriverCbs;
    
    // ------------------------------------------------------------------------
    // Function is called before is transaction sended (modification of
    // transaction)
    virtual task pre_tx(BusMasterTransaction transaction);
      // By default, callback does nothing
    endtask
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction sended (scoreboard)
    // transaction)
    virtual task post_tx(BusMasterTransaction transaction);
      // By default, callback does nothing
    endtask
  
  endclass : BmDriverCbs



  // --------------------------------------------------------------------------
  // -- Bus Master Driver Class
  // --------------------------------------------------------------------------
  class BusMasterDriver;

    // ---------------------
    // -- Class Atributes --
    // ---------------------
    BmDriverCbs cbs[$];                      // Calls backs
    virtual iIbEndpointMaster.driver BM;     // Bus Master Interface
    tBmTransMbx bmTransMbx;                  // BM Transaction MailBox
    integer enabled;                         // Driver is enabled


    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class connected to interface with transaction mailbox
    function new ( tBmTransMbx                      bmTransMbx,
                   virtual iIbEndpointMaster.driver BM);
      this.BM = BM;
      this.bmTransMbx = bmTransMbx;
      this.BM.GLOBAL_ADDR  = 64'h0000000000000000;
      this.BM.LOCAL_ADDR   = 32'h00000000;
      this.BM.LENGTH       = 12'h000;
      this.BM.TAG          = 16'h0000;
      this.BM.TRANS_TYPE   =  2'b00;
      this.BM.REQ          = 0;

      this.enabled = 0; // Driver is disabled by default
    endfunction
    
    // -- Set Callbacks -------------------------------------------------------
    // 
    task setCallbacks(BmDriverCbs cbs);
      this.cbs.push_back(cbs);
    endtask : setCallbacks
    
    // -- Enable Driver -------------------------------------------------------
    // Enable generator
    task setEnabled();
      enabled = 1;
      fork
        run();
      join_none;
    endtask : setEnabled
        
    // -- Disable Driver ------------------------------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0;
    endtask : setDisabled
    
    // -- Send Transaction ----------------------------------------------------
    // Send transaction to interface
    task sendTransaction( BusMasterTransaction transaction );
      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(transaction); 
      // Wait before sending transaction
      repeat (transaction.txDelay) @(posedge BM.CLK);
      // Write info
      //$write("@");//%t:", $realtime);
      //transaction.display();

      // Send transaction
      BM.GLOBAL_ADDR = transaction.globalAddr;
      BM.LOCAL_ADDR  = transaction.localAddr;
      BM.LENGTH      = transaction.length;
      BM.TAG         = transaction.tag;
      BM.TRANS_TYPE  = transaction.transType;
      BM.REQ         = 1;

      waitForACK();

      this.BM.GLOBAL_ADDR  = 64'h0000000000000000;
      this.BM.LOCAL_ADDR   = 32'h00000000;
      this.BM.LENGTH       = 12'h000;
      this.BM.TAG          = 16'h0000;
      this.BM.TRANS_TYPE   =  2'b00;
      this.BM.REQ          = 0;
 
      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(transaction);
    endtask : sendTransaction

    // ---------------------------
    // -- Private Class Methods --
    // ---------------------------
    
    // -- Run Driver ----------------------------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
      BusMasterTransaction transaction;
      @(posedge BM.CLK);
      while (enabled) begin            // Repeat while enabled
        bmTransMbx.get(transaction);   // Get transaction from mailbox
        sendTransaction(transaction);  // Send Transaction
      end
    endtask : run

    // -- Wait for ACK --------------------------------------------------------
    // Wait for BM acknowledge, ignore short invalid ticks
    task waitForACK();
      do begin
        @(posedge BM.CLK && BM.ACK  == 1); // wait for ACK
        @(negedge BM.CLK);                 // wait for negative edge
      end      
      while (BM.ACK == 0);                 // keep waiting if it was short 
      @(posedge BM.CLK);                   // invalid tick
    endtask : waitForACK

    
endclass


endpackage : bm_driver_pkg










