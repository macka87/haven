/*
 * sum_misc_driver.sv: Driver for Status Update Manager MISC interface
 * Copyright (C) 2009 CESNET
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
 * $Id: sum_misc_driver.sv 10960 2009-09-02 11:41:12Z xsanta06 $
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  // -- SUM MISC Driver Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to SUM MISC
   * interface. Transactions are received by 'transMbx'(Mailbox) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. You can send your custom
   * transaction by calling "sendTransaction" function.
   */
  class SumMiscDriver #(int pFlows=4, int pBlockSize=4);

    // -- Private Class Atributes --
    string    inst;                          // Driver identification
    bit       enabled;                       // Driver is enabled
    virtual iSum.misc_tb #(pFlows,pBlockSize) misc;
  
    // ----
    rand int intBit;    // Choose which bit will be setting

    rand bit enDelay;   // Enable/Disable delays between transactions
      // Enable/Disable delays between transaction (weights)
      int delayEn_wt             = 1; 
      int delayDisable_wt        = 3;

    rand int delay; // Delay between transactions
      // Delay between transactions limits
      int delayLow          = 0;
      int delayHigh         = 3;
    // ----

    // -- Constrains --
    constraint cDelays {
      intBit inside {
                     [0:2*pFlows-1]
                    };       

      enDelay dist { 1'b1 := delayEn_wt,
                     1'b0 := delayDisable_wt
                   };

      delay inside {
                    [delayLow:delayHigh]
                   };
          }
    
    
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create driver object 
    function new ( string inst, 
                   virtual iSum.misc_tb #(pFlows,pBlockSize) misc
                         );
      this.enabled     = 0;            // Driver is disabled by default
      this.misc        = misc;         // Store pointer interface 
      this.inst        = inst;         // Store driver identifier

      this.misc.misc_cb.FLUSH    <= 0;
    endfunction: new  
    
    // -- Enable Driver -------------------------------------------------------
    // Enable driver and runs driver process
    task setEnabled();
      enabled = 1; // Driver Enabling
    endtask : setEnabled

    // -- Disable Driver ------------------------------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0; // Disable driver, after sending last transaction it ends
    endtask : setDisabled
    
    // -- Set Flush -----------------------------------------------------------
    // Randomly set FLUSH signal
    task setFlush();
      bit[2*pFlows-1:0] flush = 0;

      while (flush!='1) begin
        assert(randomize());

        // Wait before setting FLUSH
        if (enDelay) repeat (delay) @(misc.misc_cb);
            
        // Set FLUSH bit to 1
        flush[intBit] = 1;
        misc.misc_cb.FLUSH <= flush;
        @(misc.misc_cb);
      end

    endtask : setFlush

  endclass: SumMiscDriver
