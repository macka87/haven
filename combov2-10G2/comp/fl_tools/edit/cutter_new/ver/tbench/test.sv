/*
 * test.sv: IB_SWITCH automatic test
 * Copyright (C) 2009 CESNET
 * Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz>
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
 * $Id: test.sv 10700 2009-08-25 14:44:13Z xstour03 $
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
// ADD FRAMELINK INTERFACES IF NEEDED
program TEST (
  input  logic     CLK,
  output logic     RESET,
  iFrameLinkRx.tb  RX,
  iFrameLinkTx.tb  TX,
  iFrameLinkTx.monitor MONITOR,
  iExt_data.monitor EXT_MONITOR
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
 
  // IF COMPONENT HAS MORE DRIVERS OR MONITORS IT IS NECESSARY TO DECLARE THEM HERE
  // AND INSTANCE THEM IN CREATEENVIRONMENT TASK
  
  FrameLinkTransaction                 flBlueprint;                             // Transaction
  Generator                            generator;                               // Generator
  FrameLinkDriver #(DRIVER0_DATA_WIDTH, DRIVER0_DREM_WIDTH)     flDriver;       // Driver
  FrameLinkMonitor #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH)  flMonitor;      // Monitor
  ExtMonitor #(EXT_SIZE, MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) extMonitor;  // Extracted data monitor
  FrameLinkResponder #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH)  flResponder;  // Responder
  Scoreboard #(RX_DATA_WIDTH, PART, EXT_OFFSET, EXT_SIZE,
               CUT_OFFSET, CUT_SIZE, GENERATOR0_FL_PACKET_COUNT) scoreboard;  // Scoreboard
  Coverage #(RX_DATA_WIDTH,RX_DREM_WIDTH,TX_DATA_WIDTH,TX_DREM_WIDTH) coverage; // Coverage
  
  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createGeneratorEnvironment(int packet_count = GENERATOR0_FL_PACKET_COUNT,
                                  int packet_size_max[] = GENERATOR0_FL_PACKET_SIZE_MAX,
                                  int packet_size_min[] = GENERATOR0_FL_PACKET_SIZE_MIN
                                  );
  // Create generator
    generator = new("Generator0", 0);
      flBlueprint = new;
      flBlueprint.packetCount   = packet_count;
      flBlueprint.packetSizeMax = packet_size_max;
      flBlueprint.packetSizeMin = packet_size_min;
      generator.blueprint       = flBlueprint;
  endtask: createGeneratorEnvironment    

  task createEnvironment();    
    // Create driver    
    flDriver  = new ("Driver0", generator.transMbx, RX);
      flDriver.txDelayEn_wt             = DRIVER0_DELAYEN_WT; 
      flDriver.txDelayDisable_wt        = DRIVER0_DELAYDIS_WT;
      flDriver.txDelayLow               = DRIVER0_DELAYLOW;
      flDriver.txDelayHigh              = DRIVER0_DELAYHIGH;
      flDriver.insideTxDelayEn_wt       = DRIVER0_INSIDE_DELAYEN_WT; 
      flDriver.insideTxDelayDisable_wt  = DRIVER0_INSIDE_DELAYDIS_WT;
      flDriver.insideTxDelayLow         = DRIVER0_INSIDE_DELAYLOW;
      flDriver.insideTxDelayHigh        = DRIVER0_INSIDE_DELAYHIGH;
    // Create monitor
    flMonitor = new ("Monitor0", MONITOR);
    extMonitor = new ("ExtMonitor0", EXT_MONITOR, MONITOR);
    // Create responder
    flResponder = new ("Responder0", TX);
      flResponder.rxDelayEn_wt            = MONITOR0_DELAYEN_WT; 
      flResponder.rxDelayDisable_wt       = MONITOR0_DELAYDIS_WT;
      flResponder.rxDelayLow              = MONITOR0_DELAYLOW;
      flResponder.rxDelayHigh             = MONITOR0_DELAYHIGH;
      flResponder.insideRxDelayEn_wt      = MONITOR0_INSIDE_DELAYEN_WT; 
      flResponder.insideRxDelayDisable_wt = MONITOR0_INSIDE_DELAYDIS_WT;
      flResponder.insideRxDelayLow        = MONITOR0_INSIDE_DELAYLOW;
      flResponder.insideRxDelayHigh       = MONITOR0_INSIDE_DELAYHIGH;    
    // Create scoreboard
    scoreboard = new;
    // Coverage class
    // NECESSARY TO CALL APROPRIATE COVERAGE IN THE CASE OF MORE INTERFACES ARE USED
    coverage = new();
      coverage.addFrameLinkInterfaceRx(RX,"RXcoverage");
      coverage.addFrameLinkInterfaceTx(MONITOR,"TXcoverage");
    // Set Callbacks
    // NECESSARY TO CALL APROPRIATE CALLBACKS IN THE CASE OF MORE DRIVERS OR MONITORS ARE USED
      flDriver.setCallbacks(scoreboard.driverCbs);
      flMonitor.setCallbacks(scoreboard.monitorCbs);
      extMonitor.setCallbacks(scoreboard.ext_monitorCbs);
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
  // Enable test Environment
  task enableTestEnvironment();
    // Enable Driver, Monitor, Coverage for each port
    // TURN ON ALL USED DRIVERS, MONITORS AND RESPONDERS IF NEEDED
    flDriver.setEnabled();
    flMonitor.setEnabled();
    extMonitor.setEnabled();
    flResponder.setEnabled();
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
     // TURN OFF ALL USED DRIVERS, MONITORS AND RESPONDERS IF NEEDED
     // Disable drivers
     #(1000*CLK_PERIOD); 
     flDriver.setDisabled();
     // Disable monitors
     flMonitor.setDisabled();
     extMonitor.setDisabled();
     flResponder.setDisabled();
     coverage.setDisabled();
  endtask : disableTestEnvironment

  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Test Case 1
  task test1();
    resetDesign(); // Reset design
    createGeneratorEnvironment();

    createEnvironment(); // Create Test Enviroment

     $write("\n\n############ TEST CASE 1 ############\n\n");
     // Enable Test environment
     enableTestEnvironment();
     // Run generators
     generator.setEnabled(TRANSACTION_COUT);

     // Do nothing if generator is active
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
  task test2(int pPART_COUNT);
    resetDesign(); // Reset design
    createGeneratorEnvironment(pPART_COUNT, '{155, 155}, '{1, 1});
    createEnvironment(); // Create Test Enviroment

     $write("\n\n############ TEST CASE 2 ############\n\n");
     // Enable Test environment
     enableTestEnvironment();
     // Run generators
     generator.setEnabled(TRANSACTION_COUT);

     // Do nothing if generator is active
     while (generator.enabled)
       #(CLK_PERIOD);
     
     // Disable Test Enviroment
     disableTestEnvironment();

     // Display Scoreboard
     scoreboard.display();
     coverage.display();
  endtask: test2

  // --------------------------------------------------------------------------
  // Test Case 3
  task test3(int pPART_COUNT);
    resetDesign(); // Reset design
    createGeneratorEnvironment(pPART_COUNT, '{36}, '{1});
    createEnvironment(); // Create Test Enviroment

     $write("\n\n############ TEST CASE 3 ############\n\n");
     // Enable Test environment
     enableTestEnvironment();
     // Run generators
     generator.setEnabled(TRANSACTION_COUT);

     // Do nothing if generator is active
     while (generator.enabled)
       #(CLK_PERIOD);

     // Disable Test Enviroment
     disableTestEnvironment();

     // Display Scoreboard
     scoreboard.display();
     coverage.display();
  endtask: test3
  
  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    int pDATA_WIDTH, pPART, pEXT_OFFSET, pEXT_SIZE, pCUT_OFFSET, pCUT_SIZE, pPART_COUNT;
    // -------------------------------------
    // TESTING
    // -------------------------------------

    pDATA_WIDTH   = RX_DATA_WIDTH;
    pPART         = PART;
    pEXT_OFFSET   = EXT_OFFSET;
    pEXT_SIZE     = EXT_SIZE;
    pCUT_OFFSET   = CUT_OFFSET;
    pCUT_SIZE     = CUT_SIZE;
    pPART_COUNT   = GENERATOR0_FL_PACKET_COUNT;

    $write("Generics setting:
            DATA_WIDTH:\t%1d
            PART:\t\t%1d
            EXT_OFFSET:\t%1d
            EXT_SIZE:\t%1d
            CUT_OFFSET:\t%1d
            CUT_SIZE:\t%1d
            PART_COUNT:\t%1d", pDATA_WIDTH, pPART, pEXT_OFFSET, pEXT_SIZE, pCUT_OFFSET, pCUT_SIZE, pPART_COUNT);
    test1();
    pPART_COUNT = 2;
    $write("PART_COUNT:\t%d\n", pPART_COUNT);
    test2(pPART_COUNT);
    pPART_COUNT = 1;
    $write("PART_COUNT:\t%d\n", pPART_COUNT);
    test3(pPART_COUNT);

    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $stop();       // Stop testing
  end

endprogram

