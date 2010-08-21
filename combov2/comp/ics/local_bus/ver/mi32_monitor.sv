  /*
 * mi32_monitor.sv: Mi32 Monitor
 * Copyright (C) 2010 CESNET
 * Author(s): Marek Santa <santa@liberouter.org>
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
 * $Id: mi32_monitor.sv 13182 2010-03-10 09:21:11Z xsanta06 $
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  // -- Mi32 Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for creating transaction objects from Mi32
   * interface signals. After is transaction received it is sended by callback 
   * to processing units (typicaly scoreboard) Unit must be enabled by 
   * "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call. You can receive your custom transaction by calling 
   * "receiveTransaction" function.
   */
  class Mi32Monitor extends Monitor;

    // -- Private Class Atributes --
    virtual iMi32.tb    mi;
  
    rand bit enTxDelay;   // Enable/Disable delays between transactions
      // Enable/Disable delays between transaction (weights)
      int txDelayEn_wt             = 1; 
      int txDelayDisable_wt        = 3;

    rand integer txDelay; // Delay between transactions
      // Delay between transactions limits
      int txDelayLow          = 0;
      int txDelayHigh         = 3;
    // ----

    // -- Constrains --
    constraint cDelays {
      enTxDelay dist { 1'b1 := txDelayEn_wt,
                       1'b0 := txDelayDisable_wt
                     };

      txDelay inside {
                      [txDelayLow:txDelayHigh]
                     };
      }

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create monitor object 
    function new ( string inst, 
                   virtual iMi32.tb mi 
                         );
      super.new(inst);

      this.mi          = mi;           // Store pointer interface 

      this.mi.cb.ADDR      <= 0;
      this.mi.cb.DRD       <= 0;
      this.mi.cb.DWR       <= 0;
      this.mi.cb.BE        <= 0;
      this.mi.cb.RD        <= 0;
      this.mi.cb.WR        <= 0;
      this.mi.cb.ARDY      <= 0;
      this.mi.cb.DRDY      <= 0;
    endfunction: new  
    
    // -- Wait for ARDY -----------------------------------------------------
    // Wait for address ready signal
    task waitForARDY();
      while (mi.cb.ARDY == 0) begin
        @(mi.cb);
      end;
    endtask : waitForARDY

    // -- Wait for DRDY -----------------------------------------------------
    // Wait for data ready signal
   task waitForDRDY();
      while (mi.cb.DRDY == 0) begin
        @(mi.cb);
      end;
    endtask : waitForDRDY

    // -- Execute transaction -----------------------------------------------
    // Send transaction command and receive data
    task executeTransaction(Mi32Transaction tr);
    
      // Allign data from transaction to fl.DATA
      mi.cb.ADDR      <= tr.address;
      mi.cb.BE        <= tr.be;     
      mi.cb.WR        <= tr.rw;  // wr == 1 => write request 
      mi.cb.RD        <= !tr.rw; // wr == 0 => read request 
      
      @(mi.cb);
      waitForARDY();  // Wait until oposit side set ready

      // clear pending request signals
      mi.cb.WR        <= 0;
      mi.cb.RD        <= 0;

      waitForDRDY();  // Wait until oposit side set data ready

      tr.data = mi.cb.DRD;   // Store received data
      
    endtask : executeTransaction
     
  endclass : Mi32Monitor 

