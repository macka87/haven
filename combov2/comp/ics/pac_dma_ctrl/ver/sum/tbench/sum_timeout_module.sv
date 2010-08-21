/*
 * sum_timeout_module.sv: Module for setting SUM timeout
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
 * $Id: sum_timeout_module.sv 11736 2009-10-25 11:01:35Z xsanta06 $
 *
 * TODO:
 *
 */
 
  import test_pkg::*; // Import CLK_PERIOD

  // --------------------------------------------------------------------------
  // -- SUM Timeout Module Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating transactions for setting
   * timeout. Transactions are sended by 'transMbx'(Mailbox) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call.   
   */
  class SumTimeoutModule #(int pFlows=4);

    // -- Private Class Atributes --
    string    inst;                          // Module identification
    bit       enabled;                       // Module is enabled
    tTransMbx transMbx;                      // MI32 transaction mailbox
    int       timeoutQue[$];                 // Queue for new timeouts
  
    // ----
    rand int timeout; // Delay between transactions
      // Delay between transactions limits
      int timeoutLow          = 5000;
      int timeoutHigh         = 10000;
    // ----

    // -- Constrains --
    constraint cDelays {
      timeout inside {
                      [timeoutLow:timeoutHigh]
                     };
          }
    
    
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create module object 
    function new ( string inst, 
                   tTransMbx transMbx 
                         );
      this.enabled     = 0;            // Module is disabled by default
      this.transMbx    = transMbx;     // Store pointer to mailbox
      this.inst        = inst;         // Store module identifier

    endfunction: new  
    
    // -- Enable Module -------------------------------------------------------
    // Enable module and runs module process
    task setEnabled();
      enabled = 1; // Module Enabling
      fork         
        run();                  // Creating module subprocess
      join_none;                // Don't wait for ending
    endtask : setEnabled

    // -- Disable Module ------------------------------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0; // Disable module
    endtask : setDisabled
    
    // -- Set New Timeout -----------------------------------------------------
    // Set new request for timeout
    task setNewTimeout(int flow);
      timeoutQue.push_back(flow);
    endtask : setNewTimeout
    
    // -- Run Modul ----------------------------------------------------------
    // Create MI32 timeout transaction and push it into mailbox
    task run();
      Mi32Transaction tr = new();

      for(int i=0; i<2*pFlows; i++) begin
        // Set MI32 timeout transaction
        assert(randomize());              // Randomize timeout
        tr.address = {i, 6'h10};
        tr.data    = timeout;
        tr.be      = '1;
        tr.rw      = 1;

        // Put transaction to mailbox
        transMbx.put(tr.copy());
      end  

      while (enabled) begin              // Repeat while enabled
        // Wait for new timeout request
        while(timeoutQue.size()==0) #CLK_PERIOD;

        // Set MI32 timeout transaction
        assert(randomize());              // Randomize timeout
        tr.address = {timeoutQue.pop_front(), 6'h10};
        tr.data    = timeout;
        tr.be      = '1;
        tr.rw      = 1;

        // Put transaction to mailbox
        transMbx.put(tr.copy());
      end

    endtask : run

  endclass: SumTimeoutModule
