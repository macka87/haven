/*!
 * \file driver.sv
 * \brief Driver class
 * \author Marek Santa <xsanta06@stud.fit.vutbr.cz>
 * \date 2009
 */  
 /* 
 * Copyright (C) 2009 CESNET
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
 * $Id: driver.sv 12327 2009-12-24 00:56:22Z xsanta06 $
 *
 */
 
  
  // --------------------------------------------------------------------------
  // -- Driver Class
  // --------------------------------------------------------------------------
  
  /*!
   * \brief Driver
   * 
   * This class is parent class for any driver. Transactions are received by 
   * 'transMbx' (Mailbox) property. Unit must be enabled by "setEnable()" 
   * function call. Generation can be stoped by "setDisable()" function call. 
   * You can send your custom transaction by calling "sendTransaction" function.
   */
  class Driver;
    
    // -- Public Class Atributes --
    //! Driver identification
    string    inst;
    //! Driver enabling
    bit       enabled;
    //! Driver is sending transaction
    bit       busy;
    //! Transaction mailbox
    tTransMbx transMbx;
    //! Callback list
    DriverCbs cbs[$];

    // ----
    //! Enable/Disable delays between transactions
    rand bit enDelay;
      //! Enable/Disable delays between transaction (weights)
      int delayEn_wt             = 1; 
      int delayDisable_wt        = 3;

    //! Delay between transactions
    rand int delay;
      //! Delay between transactions limits
      int delayLow          = 0;
      int delayHigh         = 3;
    // ----

    //! Constrains
    constraint cDelays {
      enDelay dist { 1'b1 := delayEn_wt,
                     1'b0 := delayDisable_wt
                   };

      delay inside {
                    [delayLow:delayHigh]
                   };
      }

    
    // -- Public Class Methods --

    // ------------------------------------------------------------------------
    //! Constructor 
    /*!
     * Creates driver object 
     */     
    function new ( string inst, tTransMbx transMbx );

      this.enabled     = 0;            // Driver is disabled by default
      this.busy        = 0;            // Driver is not busy by default   
      this.transMbx    = transMbx;     // Store pointer to mailbox
      this.inst        = inst;         // Store driver identifier

    endfunction: new          
    
    // ------------------------------------------------------------------------
    //! Enable Driver 
    /*!
     * Enable Driver and runs Driver process
     */     
    virtual task setEnabled();
      enabled = 1; // Driver Enabling
      fork         
         run();                // Creating driver subprocess
      join_none;               // Don't wait for ending
    endtask : setEnabled
        
    // ------------------------------------------------------------------------
    //! Disable Driver 
    virtual task setDisabled();
      enabled = 0; // Disable Driver
    endtask : setDisabled

    // ------------------------------------------------------------------------
    //! Set Callback
    /*!
     * Put callback object into List 
     */
    virtual function void setCallbacks(DriverCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks
    
    // ------------------------------------------------------------------------
    //! Send Transaction
    /* 
     * Send transaction to interface
     * \param transaction - transaction
     */
    task sendTransaction( Transaction transaction );
    endtask : sendTransaction
    
    // -- Private Class Methods --
    
    // ------------------------------------------------------------------------
    //! Run Driver
    /*!
     * Take transactions from mailbox and send it to interface
     */      
    virtual task run();
    endtask : run

  endclass : Driver
