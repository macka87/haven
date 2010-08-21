/*
 * pcie_responder.sv: Pcie Responder
 * Copyright (C) 2008 CESNET
 * Author(s): Petr Kobierský <kobiersky@liberouter.cz>
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
 * $Id: pcie_responder.sv 3855 2008-07-23 06:06:44Z xkobie00 $
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  // -- Frame Link Responder Class
  // --------------------------------------------------------------------------
  /* This class is responsible for random intra- and intertransaction's dealys. 
   * It's used by class monitor. Unit must be enabled by "setEnable()" function
   * call. Random delaying can be stoped by "setDisable()" function call.
   */
  class PcieResponder;
    
    // -- Private Class Atributes --
    string  inst;                            // Responder identification
    bit     enabled;                         // Responder is enabled
    virtual iPcieTx.responder pcie;
    
    // ----
    rand bit enRxDelay;   // Enable/Disable delays between transactions
   
    // Enable/Disable delays between transaction (weights)
    int rxDelayEn_wt             = 1; 
    int rxDelayDisable_wt        = 3;
   
    // -- Constrains --
    constraint cDelays {
      enRxDelay dist { 1'b1 := rxDelayEn_wt,
                       1'b0 := rxDelayDisable_wt
                     };
      }

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string  inst,
                   virtual iPcieTx.responder pcie
                   );
      this.enabled     = 0;           // Monitor is disabled by default   
      this.pcie        = pcie;        // Store pointer interface 
      this.inst        = inst;        // Store driver identifier
      
      // Setting default values for Frame Link interface
      pcie.cb_responder.DST_RDY_N <= 0;   // Ready even if disabled
      pcie.cb_responder.LNK_UP_N  <= 0;
      pcie.cb_responder.DST_DSC_N <= 1;
      pcie.cb_responder.BUF_AV    <= 3'b111;
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
      pcie.cb_responder.DST_RDY_N   <= 0;
    endtask : setDisabled 
    
    
    // -- Run Responder ---------------------------------------------------------
    // 
    task run();
      while (enabled) begin              // Repeat in forewer loop
        assert(randomize());
        if (enRxDelay) begin
          pcie.cb_responder.DST_RDY_N   <= 1;
          @(pcie.cb_responder);
          pcie.cb_responder.DST_RDY_N   <= 0;
          end
        else
          @(pcie.cb_responder);
        end
    endtask : run
   
  endclass: PcieResponder
