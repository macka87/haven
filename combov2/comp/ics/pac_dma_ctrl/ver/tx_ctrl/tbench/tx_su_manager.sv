/*
 * tx_su_manager.sv: Status update manager for TX PAC DMA Controller
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
 * $Id: tx_su_manager.sv 9259 2009-07-09 14:48:03Z xsanta06 $
 *
 * TODO:
 *
 */

  import math_pkg::*;

  // --------------------------------------------------------------------------
  // -- Status update manager Class 
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to STATUS_UPDATE
   * interface and releasing data form RAM. Unit must be enabled by 
   * "setEnable()" function call. Generation can be stoped by "setDisable()" 
   * function call. 
   */
  class TxSuManager #(int pFlows = 2, int pNumFlags = 8, 
                      int pRamSize = 4096, int pMaxDescLength = 1520);
    
    // ----------------------
    // -- Class Attributes --
    // ----------------------
    string    inst;                             // Manager identification
    bit       enabled;                          // Manager is enabled
    DriverCbs cbs[$];                           // Callbacks list
    virtual iPacDmaCtrl.stattx_tb #(pFlows) su;

    TxDmaCtrlDriver #(pFlows, pNumFlags, pRamSize, pMaxDescLength) ramDriver;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create Status Manager Manager object 
    function new ( string inst, 
                   TxDmaCtrlDriver #(pFlows, pNumFlags, pRamSize, 
                                     pMaxDescLength) ramDriver,
                   virtual iPacDmaCtrl.stattx_tb #(pFlows) su
                   );      
      this.enabled     = 0;            // Manager is disabled by default
      this.inst        = inst;         // Store manager identifier
      this.ramDriver   = ramDriver;
      this.su          = su;           // Store pointer interface 
      
      this.su.stattx_cb.SU_HFULL    <= 0;
      
    endfunction: new          
    
    // -- Enable Status Update Manager ----------------------------------------
    // Enable Status Update Manager and runs Status Update Manager process
    task setEnabled();
      enabled = 1; // Status Update Manager Enabling
      fork         
        run();     // Creating manager subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Status Update Manager ---------------------------------------
    // Disable Status Update Manager
    task setDisabled();
      enabled = 0; // Status Update Manager Disabling
    endtask : setDisabled

    // -- Run Status Upadte Manager -------------------------------------------
    // Receives Status Update information and send them to RAM Driver 
    task run();
      logic [log2(pFlows)-1:0] flow;
      logic [pNumFlags-1:0] flags;

      while (enabled) begin                    // Repeat while enabled        
        // Receive Status update
        receiveUpdate(flow, flags);
        // Send update to RAM driver
        $write("Status received for flow:%0d\n",flow);
        ramDriver.sendStatusUpdate(flow, flags);
        $write("Status sended\n");
        @(su.stattx_cb);
      end
    endtask : run
  
    // -- Receive Status Update -----------------------------------------------
    // Receive Status Update information
    task receiveUpdate(inout logic [log2(pFlows)-1:0] flow, 
                       inout logic [pNumFlags-1:0] flags);
      // Wait for Data Valid
      while (!su.stattx_cb.SU_DATA_VLD) @(su.stattx_cb);

      flow  = su.stattx_cb.SU_ADDR;
      flags = su.stattx_cb.SU_DATA_TX;
    endtask : receiveUpdate

  endclass: TxSuManager 
