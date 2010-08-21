/* \file test.sv
 * \brief OBUF Module automatic test
 * \author Marek Santa <santa@liberouter.org> 
 * \date 2010 
 */
/*
 * Copyright (C) 2010 CESNET
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
 * $Id: test.sv 14773 2010-08-03 12:17:38Z xsanta06 $
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import sv_fl_pkg::*;
import sv_mi32_pkg::*;
import sv_xgmii_sdr_monitor_pkg::*;
import sv_obuf_pkg::*;
import crc32_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  output logic              RESET,
  input  logic              XGMII_CLK,
  input  logic              MI32_CLK,
  input  logic              FL_CLK,
  iXgmiiSdrTx.tb            XGMII,
//  iLinkState.tb             LINK,
  iMi32.tb                  MI32,
  iFrameLinkRx.tb           FL
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  //! Frame Link Transaction
  ObufFrameLinkTransaction  flBlueprint; 
  //! Frame Link Generator                            
  Generator                 flGenerator;
  //! FrameLink driver      
  FrameLinkDriver   #(DRIVER0_DATA_WIDTH, DRIVER0_DREM_WIDTH) flDriver;
  //! XGMII monitor                               
  XgmiiSdrMonitor           xgmiiMonitor;
  //! Scoreboard  
  XgmiiObufScoreboard #(TR_TABLE_FIRST_ONLY) obufScoreboard; 
  // Coverage                             
//  Coverage #(DRIVER0_DATA_WIDTH, CTRL_DMA_DATA_WIDTH, MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) coverage; 
  
  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // -- Create Environment ----------------------------------------------------
  //! Create Environment
  /*!
   * Function is responsible for instantiate all used classes and initiate their
   * attributes.          
   */
  task createEnvironment();  
    // Create Generators    
    flGenerator = new ("FL Generator", 0);
    flBlueprint = new;
    flBlueprint.packetCount        = FL_PART_COUNT;
    flBlueprint.packetSizeMax      = FL_PART_SIZE_MAX;
    flBlueprint.packetSizeMin      = FL_PART_SIZE_MIN;
    flBlueprint.discardZero_wt     = FL_DISCARD_ZERO_WT;
    flBlueprint.discardOne_wt      = FL_DISCARD_ONE_WT;
    flBlueprint.replaceMacZero_wt  = FL_REPLACEMAC_ZERO_WT;
    flBlueprint.replaceMacOne_wt   = FL_REPLACEMAC_ONE_WT;
    flGenerator.blueprint = flBlueprint;

    // Create scoreboard
    obufScoreboard = new("OBUF Scoreboard");   
    
    // Create driver
    flDriver = new ("FL Driver", flGenerator.transMbx, FL);
      flDriver.txDelayEn_wt            = DRIVER0_DELAYEN_WT; 
      flDriver.txDelayDisable_wt       = DRIVER0_DELAYDIS_WT;
      flDriver.txDelayLow              = DRIVER0_DELAYLOW;
      flDriver.txDelayHigh             = DRIVER0_DELAYHIGH;
      flDriver.insideTxDelayEn_wt      = DRIVER0_INSIDE_DELAYEN_WT; 
      flDriver.insideTxDelayDisable_wt = DRIVER0_INSIDE_DELAYDIS_WT;
      flDriver.insideTxDelayLow        = DRIVER0_INSIDE_DELAYLOW;
      flDriver.insideTxDelayHigh       = DRIVER0_INSIDE_DELAYHIGH;    
    flDriver.setCallbacks(obufScoreboard.driverCbs);
    
    xgmiiMonitor = new ("XGMII Monitor", XGMII);
    xgmiiMonitor.setCallbacks(obufScoreboard.monitorCbs);

  endtask : createEnvironment

  // --------------------------------------------------------------------------
  //                       Test auxilarity procedures
  // --------------------------------------------------------------------------
  
  // -- Reset Design ----------------------------------------------------------
  //! Resets design
  task resetDesign();
    RESET=1;                       // Init Reset variable
    #RESET_TIME     RESET = 0;     // Deactivate reset after reset_time
  endtask : resetDesign

  // -- Enable Test Environment -----------------------------------------------
  //! Enable Test Environment
  /*!
   * Function enables all drivers, monitors and coverages.          
   */
  task enableTestEnvironment();

    // Enable drivers
    flDriver.setEnabled();
      
    // Enable monitors
    xgmiiMonitor.setEnabled();
    
    // Enable coverage
   // coverage.setEnabled();
  endtask : enableTestEnvironment

  // -- Disable Test Environment ----------------------------------------------
  //! Disable Test Environment
  /*!
   * Function disables all drivers, monitors and coverages.          
   */
  task disableTestEnvironment();
    int i = 0;

    #(1000*FL_CLK_PERIOD);
    // Disable drivers
    flDriver.setDisabled();
      
    // Check if monitor is not receiving transaction for 100 CLK_PERIODs
    while (i<100) begin
      if (xgmiiMonitor.busy)
        i = 0;
      else i++;
      #(FL_CLK_PERIOD); 
    end

    // Disable monitors     
    xgmiiMonitor.setDisabled();
    
    // Disable coverage 
    //coverage.setDisabled();
  endtask : disableTestEnvironment

  // -- Init OBUF -------------------------------------------------------------
  //! Init OBUF
  /*!
   * 
   */
  task initObuf();
    Mi32Transaction mi32Transaction = new();
    Mi32Driver      mi32Driver      = new("Mi32 Driver", null, MI32);

    // Disable OBUF
    mi32Transaction.rw      = 1;
    mi32Transaction.be      = '1;
    mi32Transaction.address = 32'h20;
    mi32Transaction.data    = 32'h0;
    mi32Driver.sendTransaction(mi32Transaction);

    // Set MAC Address (low part)
    mi32Transaction.rw      = 1;
    mi32Transaction.be      = '1;
    mi32Transaction.address = 32'h24;
    mi32Transaction.data    = MAC_ADDRESS[47:16];//[31:0];
    mi32Driver.sendTransaction(mi32Transaction);

    mi32Transaction.rw      = 1;
    mi32Transaction.be      = 'b11;
    mi32Transaction.address = 32'h28;
    mi32Transaction.data    = MAC_ADDRESS[15:0];//[47:32];
    mi32Driver.sendTransaction(mi32Transaction);

    // Enable OBUF
    mi32Transaction.rw      = 1;
    mi32Transaction.be      = '1;
    mi32Transaction.address = 32'h20;
    mi32Transaction.data    = 32'h1;
    mi32Driver.sendTransaction(mi32Transaction);

    #(10*FL_CLK_PERIOD);
  endtask : initObuf

  // -- Read Frame Counters ---------------------------------------------------
  //! Read Frame Counters
  /*!
   * Function reads values in frame counter registers via MI32.          
   */
  task readFrameCounters();
    Mi32Transaction mi32Transaction = new();
    Mi32Driver      mi32Driver      = new("Mi32 Driver", null, MI32);
    Mi32Monitor     mi32Monitor     = new("Mi32 Monitor", MI32);
    bit [63:0] trfc;    // Total Received Frames Counter
    bit [63:0] cfc;     // Correct Frames Counter
    bit [63:0] dfc;     // Discarded Frames Counter

    // Sample the current frame counters values
    mi32Transaction.address = 32'h2C;
    mi32Transaction.data    = 32'h1;
    mi32Transaction.rw      = 1;
    mi32Transaction.be      = '1;
    mi32Driver.sendTransaction(mi32Transaction);

    mi32Transaction.rw      = 0;
    mi32Transaction.be      = '1;
    // Read Total Received Frames Counter
     // Low part
    mi32Transaction.address = 32'h00;
    mi32Monitor.executeTransaction(mi32Transaction);
    trfc[31:0]  = mi32Transaction.data;

     // High part
    mi32Transaction.address = 32'h10;
    mi32Monitor.executeTransaction(mi32Transaction);
    trfc[63:32] = mi32Transaction.data;

    // Read Correct Frames Counter
     // Low part
    mi32Transaction.address = 32'h04;
    mi32Monitor.executeTransaction(mi32Transaction);
    cfc[31:0]  = mi32Transaction.data;

     // High part
    mi32Transaction.address = 32'h14;
    mi32Monitor.executeTransaction(mi32Transaction);
    cfc[63:32] = mi32Transaction.data;

    // Read Discarded Frames Counter
     // Low part
    mi32Transaction.address = 32'h08;
    mi32Monitor.executeTransaction(mi32Transaction);
    dfc[31:0]  = mi32Transaction.data;

     // High part
    mi32Transaction.address = 32'h18;
    mi32Monitor.executeTransaction(mi32Transaction);
    dfc[63:32] = mi32Transaction.data;

    #(20*FL_CLK_PERIOD);

    // Display counters values
    $write("------------------------------------------------------------\n");
    $write("-- OBUF Frame Counters\n");
    $write("------------------------------------------------------------\n");
    $write("Total Received Frames Counter:\t %10d\n",trfc);
    $write("Correct Frames Counter:\t\t %10d\n",cfc);
    $write("Discarded Frames Counter:\t\t %10d\n",dfc);
    $write("------------------------------------------------------------\n");

  endtask : readFrameCounters

  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // -- Test Case 1 -----------------------------------------------------------
  //! Test Case 1
  /*!
   * Function is responsible for running test.          
   */
  task test1();
    $write("\n\n############ TEST CASE 1 ############\n\n");
    // Init DUT
    initObuf();

    // Set behaviour of XGMII transaction table 
    obufScoreboard.setMacAddress(MAC_ADDRESS);

    // Enable Test environment
    enableTestEnvironment();

    // Run FL Generator
    flGenerator.setEnabled(TRANSACTION_COUNT);

    // While FL Generator is active do nothing
    wait (flGenerator.enabled == 0);
    
    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    obufScoreboard.display();
//    coverage.display();
    readFrameCounters();
  endtask: test1

  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    // -------------------------------------
    // DESIGN ENVIROMENT
    // -------------------------------------
    resetDesign(); // Reset design
    #(200*FL_CLK_PERIOD);
    createEnvironment(); // Create Test Enviroment
    // -------------------------------------
    // TESTING
    // -------------------------------------
    test1();       // Run Test 1

    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $stop();       // Stop testing
  end

endprogram

