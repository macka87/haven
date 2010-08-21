/*
 * tx_misc_driver.sv: MISC interface driver for TX PAC DMA Controller
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
 * $Id: tx_misc_driver.sv 9399 2009-07-14 19:51:39Z xsanta06 $
 *
 * TODO:
 *
 */
 
  import math_pkg::*;

  // --------------------------------------------------------------------------
  // -- Misc driver Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to MISC interface.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. 
   */
  class TxMiscDriver #(int pFlows = 2);
    
    // -----------------------------
    // -- Private Class Atributes --
    // -----------------------------
    string       inst;                             // Driver identification
    bit          enabled;                          // Driver is enabled
    virtual iPacDmaCtrl.misc_tb #(pFlows) misc;

    // ----
    rand bit enDelay;   // Enable/Disable RUN delay
      // Enable/Disable RUN delay (weights)
      int delayEn_wt             = 1; 
      int delayDisable_wt        = 3;

    rand int delay; // RUN delay
      // RUN delay limits
      int delayLow          = 0;
      int delayHigh         = 3;
    // ----
    
    // -- Constrains --
    constraint cDelays {
      enDelay dist { 1'b1 := delayEn_wt,
                     1'b0 := delayDisable_wt
                   };

      delay inside {
                    [delayLow:delayHigh]
                   };
      }
   
    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create Descriptor Manager object 
    function new ( string inst, 
                   virtual iPacDmaCtrl.misc_tb #(pFlows) misc
                   );      
      this.enabled     = 0;            // Driver is disabled by default
      this.inst        = inst;         // Store manager identifier
      this.misc        = misc;         // Store pointer interface 
      
      this.misc.misc_cb.RUN     <= 0;
      
    endfunction: new          
    
    // -- Enable Misc Driver --------------------------------------------------
    // Enable Misc Driver and runs Misc Driver process
    task setEnabled();
      enabled = 1;  // Misc Driver Enabling
      fork         
        run();      // Creating driver subprocess
      join_none;    // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Misc Driver ------ ------------------------------------------
    // Disable Misc Driver
    task setDisabled();
      enabled = 0;  // Misc Driver disabling
      this.misc.misc_cb.RUN     <= 0;
    endtask : setDisabled
   
    // -- Run Misc Driver -----------------------------------------------------
    // Randomly generate RUN signal
    task run();
      int flow;

      misc.misc_cb.RUN     <= ~0;

      while (enabled) begin            // Repeat while enabled        
        assert(randomize());           // Randomize rand variables
        if (enDelay)
          misc.misc_cb.RUN[$urandom_range(pFlows)] <= $urandom_range(2);
        // Wait 
        randomWait();
        @(misc.misc_cb);
      end
    endtask : run
        
    // -- Random wait ---------------------------------------------------------
    // Random wait during sending run
    task randomWait();
      repeat (delay)
        @(misc.misc_cb);
    endtask : randomWait
    
endclass : TxMiscDriver
