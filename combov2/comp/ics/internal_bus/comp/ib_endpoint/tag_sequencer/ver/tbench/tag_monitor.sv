/*!
 * \file tag_monitor.sv
 * \brief Monitor for Tag Sequencer interface
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
 * $Id: tag_monitor.sv 14346 2010-07-13 13:38:11Z xsanta06 $
 *
 */
 
  
  // --------------------------------------------------------------------------
  // -- Tag Monitor
  // --------------------------------------------------------------------------
  
  /*!
   * \brief Tag Monitor
   * 
   * This class is responsible for creating transaction objects from Tag
   * Sequencer interface signals. After is transaction received it is sended
   * by callback to processing units (typicaly scoreboard) Unit must be enabled
   * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call.
   */
  class TagMonitor #(int pTagWidth = 8) extends Monitor;
    
    // -- Public Class Attributes --
    //! Virtual interface XGMII TX  
    virtual iTagSequencerUsr.op_tb #(pTagWidth) usr; 

    
    // -- Public Class Methods --

    // ------------------------------------------------------------------------
    //! Constructor 
    /*!
     * Creates modul object and sets default values of InternalBus interface 
     * signals 
     */     
    function new ( string inst, 
                   virtual iTagSequencerUsr.op_tb #(pTagWidth) usr
                   );
      super.new(inst);

      this.usr       = usr;        // Store pointer interface 

    endfunction: new          
    
    // ------------------------------------------------------------------------
    //! Receive Transaction
    /* 
     * Receive transaction from Tag interface
     * \param transaction - transaction
     */
    virtual task receiveTransaction( Transaction transaction );
      TagTransaction #(pTagWidth)  tr;
      $cast(tr, transaction);

      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_rx(transaction, inst);       
      
      // Receive Data
      receiveData(tr);
      
      // Necessary for not calling callback after monitor disabling
      if (!enabled) return;

      #(0); // Necessary for not calling callback before driver
        
      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_rx(transaction, inst);
      
      // Monitor received transaction and is not busy
      busy = 0;
    endtask : receiveTransaction
    
    // -- Private Class Methods --
    
    // ------------------------------------------------------------------------
    //! Run Tag Monitor
    /*!
     * Receive transactions and send them for srocessing by call back
     */      
    virtual task run();
      Transaction transaction;
      TagTransaction #(pTagWidth) tr;
            
      // Wait for clock
      @(usr.op_cb);
      
      while (enabled) begin            // Repeat while enabled
        tr = new;
        $cast(transaction, tr);
      
        // Receive Transaction
        receiveTransaction(transaction);

        // Display transaction
        `ifdef TAG_MONITOR_DEBUG
          transaction.display(inst);
        `endif
      end
    endtask : run

    // ------------------------------------------------------------------------
    //! Receive data
    /*!
     * Receive TAG transaction data
     */
    task receiveData(TagTransaction #(pTagWidth) tr);
      // Wait for DONE
      waitForDone();

      // Return if monitor was disabled while waiting for DONE
      if (!enabled) return;

      busy = 1;
      // -- Store data into transaction -- 
      tr.tag       = usr.op_cb.OP_TAG;
      tr.transType = usr.op_cb.OP_TAG[0];
      @(usr.op_cb);

    endtask : receiveData
    
    // ------------------------------------------------------------------------
    //! Wait For DONE
    /*!
     * Wait for Done signal
     */
    task waitForDone();
      while (enabled && !usr.op_cb.OP_DONE) 
        @(usr.op_cb);
    endtask : waitForDone

  endclass : TagMonitor
