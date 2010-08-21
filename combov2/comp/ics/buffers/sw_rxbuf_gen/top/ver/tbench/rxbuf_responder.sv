/*
 * rxbuf_responder.sv: SW RX Buffer Responder
 * Copyright (C) 2008 CESNET
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
 * $Id: rxbuf_responder.sv 13927 2010-06-03 14:46:50Z xkoran01 $
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  // -- SW RX Buffer Responder Class
  // --------------------------------------------------------------------------
  /* This class is responsible for random intra- and intertransaction's dealys. 
   * It's used by class monitor. Unit must be enabled by "setEnable()" function
   * call. Random delaying can be stoped by "setDisable()" function call.
   */
  class SwRxBufferResponder #(int pDataWidth=64, int pBlockSize=2, int pFlows=2, int pTotalFlowSize=16384);
    
    // -- Private Class Atributes --
    string  inst;                            // Monitor identification
    bit     enabled;                         // Monitor is enabled
    virtual iSwRxBuffer.ib_tb #(pDataWidth,pBlockSize,pFlows,pTotalFlowSize) ib;
    
    // ----
    rand bit enTxDelay;   // Enable/Disable delays between transactions
      // Enable/Disable delays between transaction (weights)
      int txDelayEn_wt             = 1; 
      int txDelayDisable_wt        = 3;
    rand integer txDelay; // Delay between transactions
      // Delay between transactions limits
      int txDelayLow          = 0;
      int txDelayHigh         = 3;
    // ----


    // ----
    rand bit enInsideTxDelay;     // Enable/Disable delays inside transaction
      // Enable/Disable delays inside transaction weights
      int insideTxDelayEn_wt       = 1; 
      int insideTxDelayDisable_wt  = 3;
      // Minimal/Maximal delay between transaction words
      int insideTxDelayLow         = 0;
      int insideTxDelayHigh        = 3;
    // ----

    // -- Constrains --
    constraint cDelays {
      enTxDelay dist { 1'b1 := txDelayEn_wt,
                       1'b0 := txDelayDisable_wt
                     };

      txDelay inside {
                      [txDelayLow:txDelayHigh]
                     };

      enInsideTxDelay dist { 1'b1 := insideTxDelayEn_wt,
                             1'b0 := insideTxDelayDisable_wt
                     };
      }

    
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   virtual iSwRxBuffer.ib_tb #(pDataWidth,pBlockSize,pFlows,pTotalFlowSize) ib
                   );
      this.enabled     = 0;           // Monitor is disabled by default   
      this.ib          = ib;          // Store pointer interface 
      this.inst        = inst;        // Store driver identifier
      
      // Setting default values for Frame Link interface
      ib.ib_cb.RD_DST_RDY <= 1;           // Ready even if disabled
      
    endfunction
    
    // -- Enable Responder ------------------------------------------------------
    // Enable responder and runs responder process
    task setEnabled();
      enabled = 1; // Monitor Enabling
      fork         
        run();     // Creating monitor subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable responder -----------------------------------------------------
    // Disable responder
    task setDisabled();
      enabled = 0; // Disable monitor, after receiving last transaction
      ib.ib_cb.RD_DST_RDY   <= 1;
    endtask : setDisabled 
    
    // -- Random not ready ----------------------------------------------------
    // Disable responder
    task randomNotReady(bit en);
      if (en) begin
        repeat ($urandom_range(2)) begin
          ib.ib_cb.RD_DST_RDY <= 0;
          @(ib.ib_cb); // Wait for send
        end;
        ib.ib_cb.RD_DST_RDY <= 1;
      end;
    endtask : randomNotReady
    
    // -- Run Responder ---------------------------------------------------------
    // 
    task run();
      while (enabled) begin              // Repeat in forewer loop
        assert(randomize());
        repeat (ib.ib_cb.RD_SRC_RDY) begin //????
          waitInsideTxDelay();
        end
        waitTxDelay();
      end
    endtask : run
    
    // -- Not ready between transactions --------------------------------------
    task waitTxDelay();
      if (enTxDelay) begin
        repeat (txDelay) begin
          ib.ib_cb.RD_DST_RDY <= 0;
          @(ib.ib_cb);
        end
        ib.ib_cb.RD_DST_RDY   <= 1;
        if (txDelay > 0) @(ib.ib_cb);
      end
    endtask : waitTxDelay

    //-- Random intertransaction wait -----------------------------------------
    function integer getInsideRandomWait();
       if (enInsideTxDelay)
         return $urandom_range(insideTxDelayLow, insideTxDelayHigh);
       else
         return 0;
    endfunction : getInsideRandomWait
        
    // -- Random wait ---------------------------------------------------------
    // Random wait during sending transaction (Set SRC_RDY to 0)
    task waitInsideTxDelay();
      int waitTime = getInsideRandomWait();

      repeat (waitTime) begin
          ib.ib_cb.RD_DST_RDY <= 0;
          @(ib.ib_cb);
        end
        ib.ib_cb.RD_DST_RDY   <= 1;
      
    endtask : waitInsideTxDelay
    
  endclass: SwRxBufferResponder
