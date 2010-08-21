/*!
 * \file monitor.sv
 * \brief Monitor class
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
 * $Id: monitor.sv 13118 2010-03-07 12:44:30Z xsanta06 $
 *
 */
 
  
  // --------------------------------------------------------------------------
  // -- Monitor Class
  // --------------------------------------------------------------------------
  
  /*!
   * \brief Monitor
   * 
   * This class is parent class for any Monitor. It is responsible for
   * creating transaction objects. Unit must be enabled by "setEnable()" 
   * function call. Monitoring can be stoped by "setDisable()" function call. 
   */
  class Monitor;
    
    // -- Public Class Atributes --
    //! Monitor identification
    string    inst;
    //! Monitor enabling
    bit       enabled;
    //! Monitor is sending transaction
    bit       busy;
    //! Callback list
    MonitorCbs cbs[$];

    
    // -- Public Class Methods --

    // ------------------------------------------------------------------------
    //! Constructor 
    /*!
     * Creates monitor object 
     */     
    function new ( string inst );

      this.enabled     = 0;            // Monitor is disabled by default
      this.busy        = 0;            // Monitor is not busy by default   
      this.inst        = inst;         // Store monitor identifier

    endfunction: new          
    
    // ------------------------------------------------------------------------
    //! Enable Monitor 
    /*!
     * Enable Monitor and runs Monitor process
     */     
    virtual task setEnabled();
      enabled = 1; // Monitor Enabling
      fork         
         run();                // Creating monitor subprocess
      join_none;               // Don't wait for ending
    endtask : setEnabled
        
    // ------------------------------------------------------------------------
    //! Disable Monitor 
    virtual task setDisabled();
      enabled = 0; // Disable Monitor
    endtask : setDisabled

    // ------------------------------------------------------------------------
    //! Set Callback
    /*!
     * Put callback object into List 
     */
    virtual function void setCallbacks(MonitorCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks
    
    // ------------------------------------------------------------------------
    //! Receive Transaction
    /* 
     * Receive transaction from interface
     * \param transaction - transaction
     */
    virtual task receiveTransaction( Transaction transaction );
      assert (0) 
        $fatal("Monitor: Task receiveTransaction must be implemented in derived class"); 
    endtask : receiveTransaction
    
    // -- Private Class Methods --
    
    // ------------------------------------------------------------------------
    //! Run Monitor
    /*!
     * Receive transactions and send them for processing by call back
     */      
    virtual task run();
      assert (0) 
        $fatal("Monitor: Task run must be implemented in derived class"); 
    endtask : run

  endclass : Monitor
