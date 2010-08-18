/*!
 * \file tag_endpoint.sv
 * \brief Endpoint for Tag Sequencer
 * \author Marek Santa <santa@liberouter.org>
 * \date 2010
 */  
 /* 
 * Copyright (C) 2010 CESNET
 *
 * LICENSE TERMS
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
 * $Id: tag_endpoint.sv 14346 2010-07-13 13:38:11Z xsanta06 $
 *
 */
 
  
  // --------------------------------------------------------------------------
  // -- Tag Endpoint
  // --------------------------------------------------------------------------
  
  /*!
   * \brief Tag Endpoint
   * 
   * This class is responsible for generating signals to Tag Sequencer interface.
   * Transactions are received by 'transMbx' (Mailbox) property. Unit must be
   * enabled by "setEnable()" function call. Generation can be stoped by 
   * "setDisable()" function call. You can send your custom transaction by
   * calling "sendTransaction" function.
   */
  class TagEndpoint #(int pTagWidth = 8);
    
    // -- Public Class Attributes --
    //! Endpoint identification
    string    inst;
    //! Endpoint enabling
    bit       enabled;
    //! Endpoint is sending/receiving transaction
    bit       busy;
    //! Tag buffer
    TagTransaction #(pTagWidth) tagBuffer[$];
    //! Virtual interface EP UP 
    virtual iTagSequencerEp.tb #(pTagWidth) ep; 
    //! Virtual interface EP DOWN 
    virtual iTagSequencerEp.op_tb #(pTagWidth) ep_op; 

    // ----
    //! Enable/Disable delays between transactions (receiving interface)
    rand bit enRxDelay;
      //! Enable/Disable delays between transaction (weights)
      int rxDelayEn_wt             = 1; 
      int rxDelayDisable_wt        = 3;

    //! Delay between transactions
    rand int rxDelay;
      //! Delay between transactions limits
      int rxDelayLow          = 2;
      int rxDelayHigh         = 3;

    //! Enable/Disable delays between transactions (transmiting interface)
    rand bit enTxDelay;
      //! Enable/Disable delays between transaction (weights)
      int txDelayEn_wt             = 1; 
      int txDelayDisable_wt        = 0;

    //! Delay between transactions
    rand int txDelay;
      //! Delay between transactions limits
      int txDelayLow          = 3;
      int txDelayHigh         = 7;
    // ----

    //! Constrains
    constraint cDelays {
      enRxDelay dist { 1'b1 := rxDelayEn_wt,
                       1'b0 := rxDelayDisable_wt
                     };

      rxDelay inside {
                      [rxDelayLow:rxDelayHigh]
                     };
                     
      enTxDelay dist { 1'b1 := txDelayEn_wt,
                       1'b0 := txDelayDisable_wt
                     };

      txDelay inside {
                      [txDelayLow:txDelayHigh]
                     };
      }

    
    // -- Public Class Methods --

    // ------------------------------------------------------------------------
    //! Constructor 
    /*!
     * Creates modul object and sets default values of Tag interface signals 
     */     
    function new ( string inst, 
                   virtual iTagSequencerEp.tb #(pTagWidth) ep,
                   virtual iTagSequencerEp.op_tb #(pTagWidth) ep_op
                   );

      this.inst      = inst;       // Store endpoint identifier
      this.enabled   = 0;          // Endpoint is disabled by default
      this.busy      = 0;          // Endpoint is not busy by default   
      this.ep        = ep;         // Store pointer interface 
      this.ep_op     = ep_op;      // Store pointer interface 

      // Setting default values for Tag interface
      this.ep.cb.ACK                 <= 0;
      this.ep_op.op_cb.OP_TAG        <= 0;
      this.ep_op.op_cb.OP_DONE       <= 0;
    endfunction: new          
    
    // ------------------------------------------------------------------------
    //! Enable Endpoint 
    /*!
     * Enable Endpoint and runs Endpoint process
     */     
    virtual task setEnabled();
      enabled = 1; // Endpoint Enabling
      fork         
         runRx();             // Creating endpoint subprocess
         runTx();             // Creating endpoint subprocess
      join_none;               // Don't wait for ending
    endtask : setEnabled
        
    // ------------------------------------------------------------------------
    //! Disable Endpoint 
    virtual task setDisabled();
      enabled = 0; // Disable Endpoint
    endtask : setDisabled

    // -- Private Class Methods --
    
    // ------------------------------------------------------------------------
    //! Run RX TAG Endpoint
    /*!
     * Receive transaction from Tag interface and store it into buffer
     */      
    virtual task runRx();
      TagTransaction #(pTagWidth) transaction;
            
      // Wait for clock
      @(ep.cb);
      
      while (enabled) begin            // Repeat while enabled
        assert(randomize(enRxDelay, rxDelay));
        transaction = new();

        // Wait before receiving transaction
        if (enRxDelay) repeat (rxDelay) @(ep.cb);

        // Wait for Request
        waitForReq();

        // Receive data
        transaction.tag       = ep.cb.TAG;
        transaction.transType = ep.cb.TRANS_TYPE;

        // Store transaction into buffer
        tagBuffer.push_back(transaction);

        ep.cb.ACK <= 1;
        @(ep.cb);
        ep.cb.ACK <= 0;
        @(ep.cb);
//        transaction.display(inst);
      end
    endtask : runRx

    // ------------------------------------------------------------------------
    //! Wait For REQ
    /*!
     * Wait for request signal
     */
    task waitForReq();
      while(!ep.cb.REQ)
        @(ep.cb);
    endtask : waitForReq
    
    // ------------------------------------------------------------------------
    //! Run TX TAG Endpoint
    /*!
     * Get transaction from buffer and send it to TAG interface
     */      
    virtual task runTx();
      TagTransaction #(pTagWidth) transaction;
      int trIndex;
            
      // Wait for clock
      @(ep_op.op_cb);
      
      while (enabled) begin            // Repeat while enabled
        assert(randomize(enTxDelay, txDelay));

        while (tagBuffer.size == 0)
          @(ep_op.op_cb);

        // Get random transaction from buffer
        trIndex = $urandom_range(tagBuffer.size()-1);
        transaction = tagBuffer[trIndex];
        tagBuffer.delete(trIndex);

        // Wait before sending transaction
        if (enTxDelay) repeat (txDelay) @(ep_op.op_cb);

        ep_op.op_cb.OP_TAG  <= transaction.tag;
        ep_op.op_cb.OP_DONE <= 1;
        @(ep_op.op_cb);
        ep_op.op_cb.OP_DONE <= 0;
//        transaction.display(inst);
      end
    endtask : runTx

  endclass : TagEndpoint
