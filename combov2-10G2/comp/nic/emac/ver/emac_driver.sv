/*!
 * \file emac_driver.sv
 * \brief Driver for EMAC interface
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
 * $Id: emac_driver.sv 15032 2010-08-13 07:29:34Z xsanta06 $
 *
 */
 
  
  // --------------------------------------------------------------------------
  // -- EMAC Driver
  // --------------------------------------------------------------------------
  
  /*!
   * \brief EMAC Driver
   * 
   * This class is responsible for generating signals to EMAC interface.
   * Transactions are received by 'transMbx' (Mailbox) property. Unit must be
   * enabled by "setEnable()" function call. Generation can be stoped by 
   * "setDisable()" function call. You can send your custom transaction by
   * calling "sendTransaction" function.
   */
  class EmacDriver extends Driver;
    
    // -- Public Class Attributes --
    //! Virtual interface EMAC RX  
    virtual iEmacRx.tb emac; 

    //! Delay inside transactions
    rand int insideDelay;
      //! Delay inside transactions limits
      int insideDelayLow          = 0;
      int insideDelayHigh         = 3;
    // ----

    //! Constrains
    constraint cDelays1 {
      insideDelay inside {
                          [insideDelayLow:insideDelayHigh]
                         };
      }
    
    // -- Public Class Methods --

    // ------------------------------------------------------------------------
    //! Constructor 
    /*!
     * Creates modul object and sets default values of InternalBus interface 
     * signals 
     */     
    function new ( string inst, 
                   tTransMbx transMbx, 
                   virtual iEmacRx.tb emac
                   );
      super.new(inst, transMbx);

      this.emac       = emac;        // Store pointer interface 

      // Setting default values for Internal Bus interface
      this.emac.cb.DATA      <= 'x;
      this.emac.cb.DVLD      <= 0;
      this.emac.cb.GOODFRAME <= 0;
      this.emac.cb.BADFRAME  <= 0;
      this.emac.cb.FRAMEDROP <= 0;
      this.emac.cb.STATS     <= 'x;
      this.emac.cb.STATSVLD  <= 0;
      this.emac.cb.STATSBYTEVLD  <= 0;
    endfunction: new          
    
    // ------------------------------------------------------------------------
    //! Send Transaction
    /* 
     * Send transaction to EMAC interface
     * \param transaction - transaction
     */
    virtual task sendTransaction( Transaction transaction );
      EmacTransaction tr;
      
      // Driver is sending transaction
      busy = 1;

      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(transaction, inst);       
      
      // Wait before sending transaction
      if (enDelay) repeat (delay) @(emac.cb);
            
      // Send transaction
      $cast(tr, transaction); 
      sendData(tr);
      
      // Set not ready 
      this.emac.cb.DVLD      <= 0;
      this.emac.cb.STATSVLD  <= 0;
    
      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(transaction, inst);
      
      // Driver is not sending transaction
      busy = 0;
    endtask : sendTransaction
    
    // -- Private Class Methods --
    
    // ------------------------------------------------------------------------
    //! Run EMAC Driver
    /*!
     * Take transactions from mailbox and generate them to interface
     */      
    virtual task run();
      Transaction transaction;
            
      // Wait for clock
      @(emac.cb);
      
      while (enabled) begin            // Repeat while enabled
        // Randomize rand variables
        assert(randomize());

        // Get transaction from mailbox 
        transMbx.get(transaction);

        // Send Transaction
        sendTransaction(transaction);

//        transaction.display(inst);
      end
    endtask : run

    // ------------------------------------------------------------------------
    //! Send data
    /*!
     * Send EMAC transaction data
     */
    task sendData(XgmiiTransaction tr);
      // Data with CRC
      byte dataWithCrc[] = {tr.data, tr.crc};

      // -- Send data --
      for (i=0; i<dataWithCrc.size; i++) begin
        emac.cb.DATA <= dataWithCrc[i];
        emac.cb.DVLD <= 1; 
        @(emac.cb);
      end

      emac.cb.DVLD <= 0; 

      fork
        begin
          // -- Set Good/Bad Frame
          repeat (insideDelay) @(emac.cb);
          emac.cb.GOODFRAME <= tr.stats[0];
          emac.cb.BADFRAME  <= tr.stats[1];
          emac.cb.FRAMEDROP <= 0;
        end
        begin
          // -- Send stats --
          for (int i=0; i<4; i++);
            emac.cb.STATS    <= (tr.stats >> i*7) && 7'b1111111;
            emac.cb.STATSVLD <= 1;
            @(emac.cb);
          end
          emac.cb.STATSVLD <= 1;
        end
      join;   

    endtask : sendData
    
  endclass : EmacDriver
