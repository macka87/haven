/*!
 * \file sampling_unit.sv
 * \brief BFM for Sampling Unit interface
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
 * damages (including, but not limited to, procurement of saubstitute
 * goods or services; loss of use, data, or profits; or business
 * interruption) however caused and on any theory of liability, whether
 * in contract, strict liability, or tort (including negligence or
 * otherwise) arising in any way out of the use of this software, even
 * if advised of the possibility of sauch damage.
 *
 * $Id: sampling_unit.sv 12661 2010-02-09 02:15:23Z xsanta06 $
 *
 */
 
  
  // --------------------------------------------------------------------------
  // -- Sampling Unit
  // --------------------------------------------------------------------------
  
  /*!
   * \brief Sampling Unit
   * 
   * This class is responsible for generating signals Sampling Unit interface.
   * Unit must be enabled by "setEnable()" function call. Generation can be 
   * stoped by "setDisable()" function call.
   */
  class SamplingUnit;
    
    //! BFM identification
    string    inst;
    //! BFM enabling
    bit       enabled;
    //! Callback list
    ScoreboardSamplingCbs cbs[$];
    //! Virtual interface Sampling Unit  
    virtual iSamplingUnit.tb sau; 

    // ----
    //! Enable/Disable delays between REQ and DV
    rand bit enDelay;
      //! Enable/Disable delays between REQ and DV (weights)
      int delayEn_wt        = 0; 
      int delayDisable_wt   = 1;

    //! Delay between REQ and DV
    rand int delay;
      //! Delay between REQ and DV limits
      int delayLow          = 0;
      int delayHigh         = 2;
    // ----

    // ----
    //! Enable/Disable sampling (setting DV without ACCEPT)
    rand bit enSampling;
      //! Sampling ratio
      int samplingEn_wt     = 1;
      int samplingDis_wt    = 0;
    // ----

    //! Constrains
    constraint cDelays {
      enDelay dist { 1'b1 := delayEn_wt,
                     1'b0 := delayDisable_wt
                   };

      delay inside {
                    [delayLow:delayHigh]
                   };

      enSampling dist { 1'b1 := samplingEn_wt,
                        1'b0 := samplingDis_wt
                      };
      }

    
    // -- Public Class Methods --

    // ------------------------------------------------------------------------
    //! Constructor 
    /*!
     * Creates BFM object and sets default values of Sampling Unit interface 
     * signals 
     */     
    function new ( string inst, 
                   virtual iSamplingUnit.tb sau
                   );
      this.enabled     = 0;            // BFM is disabled by default
      this.sau         = sau;          // Store pointer interface 
      this.inst        = inst;         // Store BFM identifier

      // Setting default values for Internal Bus interface
      this.sau.cb.ACCEPT      <= 0;
      this.sau.cb.DV          <= 0;
    endfunction: new          
    
    // ------------------------------------------------------------------------
    //! Set Callbacks
    /*! 
     * Put callback object into List 
     */
    function void setCallbacks(ScoreboardSamplingCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks
    
    // ------------------------------------------------------------------------
    //! Enable BFM 
    /*!
     * Enable BFM and runs BFM process
     */     
    task setEnabled();
      enabled = 1; // BFM Enabling
      fork         
         run();                // Creating BFM subprocess
      join_none;               // Don't wait for ending
    endtask : setEnabled
        
    // ------------------------------------------------------------------------
    //! Disable BFM 
    task setDisabled();
      enabled = 0; // Disable BFM
    endtask : setDisabled
    
    // -- Private Class Methods --
    
    // ------------------------------------------------------------------------
    //! Run Sampling Unit BFM
    /*!
     * 
     */      
    task run();
            
      bit accepted = 0;              // Set if SAU_ACCEPT is set
      @(sau.cb);                     // Wait for clock
      
      while (enabled) begin            // Repeat while enabled
        assert(randomize());           // Randomize rand variables

        // Wait for SAU_REQ
        waitForReq();

        // Wait before sending SAU_DV
        if (enDelay) repeat (delay) @(sau.cb);
            
        // Set sau_ACCEPT
        if (enSampling) begin
          sau.cb.ACCEPT <= 1;
          accepted = 1;
        end
        else accepted = 0;
          
        sau.cb.DV     <= 1;
        @(sau.cb);

        sau.cb.ACCEPT <= 0;
        sau.cb.DV     <= 0;

        // Call postprocesing, if is available
        foreach (cbs[i]) cbs[i].post_tx(accepted, inst);
      end
    endtask : run
        
    // ------------------------------------------------------------------------
    //! Wait for sau REQ 
    task waitForReq();
      while (!sau.cb.REQ) begin
        @(sau.cb);
      end;
    endtask : waitForReq

  endclass : SamplingUnit
