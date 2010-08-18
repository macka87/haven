/*
 * test.sv: IB_SWITCH automatic test
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobiersky <kobiersky@liberouter.org>
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
 * $Id: test.sv 12615 2010-02-05 09:40:25Z xvozen00 $
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import sv_fl_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic     CLK,
  output logic     RESET,
  iFrameLinkRx.tb  RX,
  iFrameLinkTx.tb  TX[OUTPUT_COUNT],
  iFrameLinkTx.monitor  MONITOR[OUTPUT_COUNT]
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  
  FrameLinkTransaction                                          flBlueprint;                  
  Generator                                                     generator; 
  FrameLinkDriver  #(DRIVER_DATA_WIDTH, DRIVER_DREM_WIDTH)      flDriver;       
  FrameLinkMonitor #(MONITOR_DATA_WIDTH, MONITOR_DREM_WIDTH)    flMonitor[OUTPUT_COUNT];
  FrameLinkResponder #(MONITOR_DATA_WIDTH, MONITOR_DREM_WIDTH)  flResponder[OUTPUT_COUNT];      
  Coverage #(RX_DATA_WIDTH,DREM_WIDTH,MONITOR_DATA_WIDTH,MONITOR_DREM_WIDTH)       coverage;
  Scoreboard #(OUTPUT_COUNT)                                    scoreboard;                              
  
  // Only array of virtual interfaces can be indexed 
  virtual iFrameLinkTx.tb      #(MONITOR_DATA_WIDTH, MONITOR_DREM_WIDTH) vTX[OUTPUT_COUNT];
  virtual iFrameLinkTx.monitor #(MONITOR_DATA_WIDTH, MONITOR_DREM_WIDTH) vMONITOR[OUTPUT_COUNT];
  
  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createGeneratorEnvironment(int packet_count = GENERATOR_FL_PACKET_COUNT,
                                  int packet_size_max[] = GENERATOR_FL_PACKET_SIZE_MAX,
                                  int packet_size_min[] = GENERATOR_FL_PACKET_SIZE_MIN
                                  );
  // Create generator
    generator= new("Generator", 0);
    flBlueprint = new;
    flBlueprint.packetCount   = packet_count;
    flBlueprint.packetSizeMax = packet_size_max;
    flBlueprint.packetSizeMin = packet_size_min;
    generator.blueprint = flBlueprint;
  endtask: createGeneratorEnvironment    
  
  // Create Test Environment
  task createEnvironment();
    // Assign virtual interfaces
    vTX      = TX;
    vMONITOR = MONITOR;
    
    // Coverage class
    coverage = new();
    // Create scoreboard
    scoreboard = new;

    // Create and connect driver
    flDriver       = new ("Driver0", generator.transMbx, RX);
      flDriver.txDelayEn_wt             = DRIVER_DELAYEN_WT; 
      flDriver.txDelayDisable_wt        = DRIVER_DELAYDIS_WT;
      flDriver.txDelayLow               = DRIVER_DELAYLOW;
      flDriver.txDelayHigh              = DRIVER_DELAYHIGH;
      flDriver.insideTxDelayEn_wt       = DRIVER_INSIDE_DELAYEN_WT; 
      flDriver.insideTxDelayDisable_wt  = DRIVER_INSIDE_DELAYDIS_WT;
      flDriver.insideTxDelayLow         = DRIVER_INSIDE_DELAYLOW;
      flDriver.insideTxDelayHigh        = DRIVER_INSIDE_DELAYHIGH;
      flDriver.setCallbacks(scoreboard.driverCbs);
      coverage.addFrameLinkInterfaceRx(RX,"RXcoverage");
        
    // Create and connect monitor and responder
    for(int i=0; i<OUTPUT_COUNT; i++) begin
      string monitorLabel;
      string responderLabel;
      
      $swrite(monitorLabel, "Monitor %0d", i);
      $swrite(responderLabel, "Responder %0d", i);
      flMonitor[i]   = new (monitorLabel, vMONITOR[i]);
      flResponder[i] = new (responderLabel, vTX[i]);
      
      flResponder[i].rxDelayEn_wt            = MONITOR_DELAYEN_WT; 
      flResponder[i].rxDelayDisable_wt       = MONITOR_DELAYDIS_WT;
      flResponder[i].rxDelayLow              = MONITOR_DELAYLOW;
      flResponder[i].rxDelayHigh             = MONITOR_DELAYHIGH;
      flResponder[i].insideRxDelayEn_wt      = MONITOR_INSIDE_DELAYEN_WT; 
      flResponder[i].insideRxDelayDisable_wt = MONITOR_INSIDE_DELAYDIS_WT;
      flResponder[i].insideRxDelayLow        = MONITOR_INSIDE_DELAYLOW;
      flResponder[i].insideRxDelayHigh       = MONITOR_INSIDE_DELAYHIGH;    
      flMonitor[i].setCallbacks(scoreboard.monitorCbs);
      coverage.addFrameLinkInterfaceTx(vMONITOR[i],"TXcoverage0");
    end;
  endtask : createEnvironment

  // --------------------------------------------------------------------------
  //                       Test auxilarity procedures
  // --------------------------------------------------------------------------
  
  // --------------------------------------------------------------------------
  // Resets design
  task resetDesign();
    RESET=1;                       // Init Reset variable
    #RESET_TIME     RESET = 0;     // Deactivate reset after reset_time
  endtask : resetDesign

  // --------------------------------------------------------------------------
  // Enable test Enviroment
  task enableTestEnvironment();
    // Enable Driver, Monitor, Coverage for each port
    flDriver.setEnabled();
    for(int i=0; i<OUTPUT_COUNT; i++) begin
      flMonitor[i].setEnabled();
      flResponder[i].setEnabled();
    end
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Enviroment
  task disableTestEnvironment();
     // Disable drivers
    #(1000*CLK_PERIOD);
    flDriver.setDisabled();
    
    // Wait for finishing transactions
    #(12000*CLK_PERIOD);
    
    // Disable monitors
    for(int i=0; i<OUTPUT_COUNT; i++) begin
      flMonitor[i].setDisabled();
      flResponder[i].setDisabled();
    end
     
    coverage.setDisabled();
  endtask : disableTestEnvironment

  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Test Case 1
  task test1();
     $write("\n\n############ TEST CASE 1 ############\n\n");
     // Enable Test enviroment
     enableTestEnvironment();
     // Run generators
     generator.setEnabled(TRANSACTION_COUNT);

     // Wait until generator generates transactions
    while (generator.enabled)
      #(CLK_PERIOD);
    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
    coverage.display();
  endtask: test1
  
  // --------------------------------------------------------------------------
  // Test Case 2
  task test2();
    $write("\n\n############ TEST CASE 2 ############\n\n");
    $write("Test checks correct packet distribution when\n");
    $write("RX_SRC_RDY_N and TX_DST_RDY_N is set to 0\n");
    $write("-------------------------------------------\n\n");
    // Enable Test enviroment
    enableTestEnvironment();

    // Set RX_SRC_RDY_N to 0
    flDriver.txDelayEn_wt             = 0; 
    flDriver.txDelayDisable_wt        = 1;
    flDriver.insideTxDelayEn_wt       = 0; 
    flDriver.insideTxDelayDisable_wt  = 1;

    // Set TX_DST_RDY_N to 0
    for (int i=0; i < OUTPUT_COUNT; i++) begin
      flResponder[i].rxDelayEn_wt            = 0; 
      flResponder[i].rxDelayDisable_wt       = 1;
      flResponder[i].insideRxDelayEn_wt      = 0; 
      flResponder[i].insideRxDelayDisable_wt = 1;
    end  

    scoreboard.enablePktCntCheck();

    // Run generators
    generator.setEnabled(TRANSACTION_COUNT);

    // Wait until generator generates transactions
    while (generator.enabled)
      #(CLK_PERIOD);
    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
    coverage.display();
  endtask: test2
  

  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    // -------------------------------------
    // DESIGN ENVIROMENT
    // -------------------------------------
    resetDesign(); // Reset design
    createGeneratorEnvironment();
    createEnvironment(); // Create Test Enviroment

    // -------------------------------------
    // TESTING
    // -------------------------------------
    $write("\n\n############ GENERICS ############\n\n");
    $write("RX_DATA_WIDTH:\t%1d\nTX_DATA_WIDTH:\t%1d\nFRAME_PARTS:\t%1d\nOUTPUT_COUNT:\t%1d\n",RX_DATA_WIDTH,TX_DATA_WIDTH,FRAME_PARTS,OUTPUT_COUNT);
    if (TEST_CASE1) test1();       // Run Test 1
    if (TEST_CASE2) test2();       // Run Test 2
    
    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
 
    $stop();       // Stop testing
  end

endprogram

