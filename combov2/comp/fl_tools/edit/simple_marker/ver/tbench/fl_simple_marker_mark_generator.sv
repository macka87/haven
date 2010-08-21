/*
 * fl_simple_marker_mark_generator.sv: FrameLink SIMPLE MARKER Mark Generator
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
 * $Id: fl_simple_marker_mark_generator.sv 10305 2009-08-12 05:34:35Z xsanta06 $
 *
 * TODO:
 *
 */
 
  import math_pkg::*;
  // --------------------------------------------------------------------------
  // -- FrameLink SIMPLE MARKER Mark Generator
  // --------------------------------------------------------------------------
  /* This class is responsible for generating marks. Unit must be enabled by 
   * "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call.
   */
  class FrameLinkSimpleMarkGenerator #(int pMarkSize=1);
    
    // -- Private Class Atributes --
    string  inst;                            // Mark generator identification
    bit     enabled;                         // Mark generator is enabled
    virtual iFrameLinkSimpleMarker.mark_tb #(pMarkSize)   markIfc;
    
    // ----
    rand bit enValidDelay;   // Enable/Disable valid delay
      // Enable/Disable valid delay (weights)
      int validDelayEn_wt             = 1; 
      int validDelayDisable_wt        = 3;

    rand int validDelay; // Valid delay
      // Valid delay
      int validDelayLow          = 0;
      int validDelayHigh         = 3;
    // ----

    // -- Constrains --
    constraint cDelays {
      enValidDelay dist { 1'b1 := validDelayEn_wt,
                          1'b0 := validDelayDisable_wt
                        };

      validDelay inside {
                         [validDelayLow:validDelayHigh]
                        };
    };


    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   virtual iFrameLinkSimpleMarker.mark_tb #(pMarkSize) markIfc
                   );
      this.enabled     = 0;           // Monitor is disabled by default     
      this.markIfc     = markIfc;     // Store pointer MARK interface 
      this.inst        = inst;        // Store mark generator identifier
      
    endfunction

    // -- Enable Mark generator -----------------------------------------------
    // Enable mark generator and runs mark generator process
    task setEnabled();
      enabled = 1; // Mark generator Enabling
      fork         
        run();     // Creating mark generator subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Mark generator ----------------------------------------------
    // Disable mark generator
    task setDisabled();
      enabled = 0; // Disable mark generator
    endtask : setDisabled 
    
    // -- Run mark generator --------------------------------------------------
    // Generate and apply mark
    task run();
      bit [pMarkSize*8-1:0] mark = 0;    // Mark
      
      while (enabled) begin              // Repeat in forever loop
        assert(randomize());
        // Set new mark
        markIfc.mark_cb.MARK_NO <= mark;     
        // Insert valid delay
        insertValidDelay();
        // Wait for mark inserting
        waitForMarkNext();
        // Next mark
        mark++;       
      end
    endtask : run
    
    // -- Wait For Mark Next --------------------------------------------------
    // Wait for MARK_NEXT
    task waitForMarkNext();
      do begin
        @(markIfc.mark_cb);
      end while (enabled && !markIfc.mark_cb.MARK_NEXT);  
    endtask : waitForMarkNext

    // ------------------------------------------------------------------------
    //! Insert Valid Delay
    /*!
     * Set random MARK_VALID signal
     */
    task insertValidDelay();
      if (enValidDelay)
        repeat (validDelay) begin
          markIfc.mark_cb.MARK_VALID <= 0;
          @(markIfc.mark_cb);
        end
      markIfc.mark_cb.MARK_VALID <= 1;
    endtask: insertValidDelay

endclass : FrameLinkSimpleMarkGenerator    
