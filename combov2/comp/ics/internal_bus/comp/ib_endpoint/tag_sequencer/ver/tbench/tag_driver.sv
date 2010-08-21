/*!
 * \file tag_driver.sv
 * \brief Driver for Tag Sequencer interface
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
 * $Id: tag_driver.sv 14346 2010-07-13 13:38:11Z xsanta06 $
 *
 */
 
  
  // --------------------------------------------------------------------------
  // -- Tag Driver
  // --------------------------------------------------------------------------
  
  /*!
   * \brief Tag Driver
   * 
   * This class is responsible for generating signals to Tag Sequencer interface.
   * Transactions are received by 'transMbx' (Mailbox) property. Unit must be
   * enabled by "setEnable()" function call. Generation can be stoped by 
   * "setDisable()" function call. You can send your custom transaction by
   * calling "sendTransaction" function.
   */
  class TagDriver #(int pTagWidth = 8) extends Driver;
    
    // -- Public Class Attributes --
    //! Virtual interface TAG USR UP  
    virtual iTagSequencerUsr.tb #(pTagWidth) usr; 

    
    // -- Public Class Methods --

    // ------------------------------------------------------------------------
    //! Constructor 
    /*!
     * Creates modul object and sets default values of Tag interface signals 
     */     
    function new ( string inst, 
                   tTransMbx transMbx, 
                   virtual iTagSequencerUsr.tb #(pTagWidth) usr
                   );
      super.new(inst, transMbx);

      this.usr       = usr;        // Store pointer interface 

      // Setting default values for Tag interface
      this.usr.cb.TAG        <= 0;
      this.usr.cb.REQ        <= 0;
      this.usr.cb.TRANS_TYPE <= 0;
    endfunction: new          
    
    // ------------------------------------------------------------------------
    //! Send Transaction
    /* 
     * Send transaction to XGMII interface
     * \param transaction - transaction
     */
    virtual task sendTransaction( Transaction transaction );
      TagTransaction #(pTagWidth) tr;
      
      // Driver is sending transaction
      busy = 1;

      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(transaction, inst);       
      
      // Wait before sending transaction
      if (enDelay) repeat (delay) @(usr.cb);
            
      // Send transaction
      $cast(tr, transaction); 
      sendData(tr);
      
      // Set not ready 
      usr.cb.REQ <= 0;
    
      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(transaction, inst);
      
      // Driver is not sending transaction
      busy = 0;
    endtask : sendTransaction
    
    // -- Private Class Methods --
    
    // ------------------------------------------------------------------------
    //! Run TAG Driver
    /*!
     * Take transactions from mailbox and generate them to interface
     */      
    virtual task run();
      Transaction transaction;
            
      // Wait for clock
      @(usr.cb);
      
      while (enabled) begin            // Repeat while enabled
        // Randomize rand variables
        assert(randomize());

        // Get transaction from mailbox 
        while (transMbx.try_get(transaction)==0) begin
          if (!enabled) return;
          @(usr.cb);
        end

        // Send Transaction
        sendTransaction(transaction);

//        transaction.display(inst);
      end
    endtask : run

    // ------------------------------------------------------------------------
    //! Send data
    /*!
     * Send Tag transaction data
     */
    task sendData(TagTransaction #(pTagWidth) tr);

      // Send data
      usr.cb.TAG        <= tr.tag;
      usr.cb.TRANS_TYPE <= tr.transType;
      usr.cb.REQ        <= 1;
      @(usr.cb);

      waitForAck();

    endtask : sendData
    
    // ------------------------------------------------------------------------
    //! Wait For ACK
    /*!
     * Wait for ACK signal
     */
    task waitForAck();

      while(!usr.cb.ACK)
        @(usr.cb);

    endtask : waitForAck
    
  endclass : TagDriver
