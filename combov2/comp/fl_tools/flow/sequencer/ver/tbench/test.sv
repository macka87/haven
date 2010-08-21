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
 * $Id: test.sv 8932 2009-06-23 01:13:49Z xsanta06 $
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
  iFrameLinkRx.tb  RX[INPUT_COUNT],
  iFrameLinkTx.tb  TX,
  iFrameLinkTx.monitor  MONITOR
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
    
  FrameLinkTransaction                                          flBlueprint;                  
  Generator                                                     generator[INPUT_COUNT]; 
  FrameLinkDriver  #(DRIVER_DATA_WIDTH, DRIVER_DREM_WIDTH)      flDriver[INPUT_COUNT];       
  FrameLinkMonitor #(MONITOR_DATA_WIDTH, MONITOR_DREM_WIDTH)    flMonitor;
  FrameLinkResponder #(MONITOR_DATA_WIDTH, MONITOR_DREM_WIDTH)  flResponder;      
  Coverage #(DRIVER_DATA_WIDTH,DRIVER_DREM_WIDTH,MONITOR_DATA_WIDTH,MONITOR_DREM_WIDTH) coverage;
  Scoreboard #(PARTS,TICKET_PART,TICKET_SIZE,TICKET_OFFSET)     scoreboard;                              
  
  // Only array of virtual interfaces can be indexed 
  virtual iFrameLinkRx.tb #(DRIVER_DATA_WIDTH, DRIVER_DREM_WIDTH) vRX[INPUT_COUNT];
  
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
    for(int i=0; i<INPUT_COUNT; i++) begin
      string generatorLabel;
      
      $swrite(generatorLabel, "Generator %0d", i);
      generator[i]= new(generatorLabel, i);
      flBlueprint = new;
      flBlueprint.packetCount   = packet_count;
      flBlueprint.packetSizeMax = packet_size_max;
      flBlueprint.packetSizeMin = packet_size_min;
      generator[i].blueprint = flBlueprint;
    end;  
  endtask: createGeneratorEnvironment    
  
  // Create Test Environment
  task createEnvironment();
    // Assign virtual interfaces
    vRX      = RX;
    // Coverage class
    coverage = new();
    // Create scoreboard
    scoreboard = new;

    // Create and connect driver
    for(int i=0; i<INPUT_COUNT; i++) begin
      string driverLabel;
      
      $swrite(driverLabel, "Driver %0d", i);
      flDriver[i]    = new (driverLabel, generator[i].transMbx, vRX[i]);
      flDriver[i].txDelayEn_wt             = DRIVER_DELAYEN_WT; 
      flDriver[i].txDelayDisable_wt        = DRIVER_DELAYDIS_WT;
      flDriver[i].txDelayLow               = DRIVER_DELAYLOW;
      flDriver[i].txDelayHigh              = DRIVER_DELAYHIGH;
      flDriver[i].insideTxDelayEn_wt       = DRIVER_INSIDE_DELAYEN_WT; 
      flDriver[i].insideTxDelayDisable_wt  = DRIVER_INSIDE_DELAYDIS_WT;
      flDriver[i].insideTxDelayLow         = DRIVER_INSIDE_DELAYLOW;
      flDriver[i].insideTxDelayHigh        = DRIVER_INSIDE_DELAYHIGH;
      flDriver[i].setCallbacks(scoreboard.driverCbs);
      coverage.addFrameLinkInterfaceRx(vRX[i],"RXcoverage");
    end;
        
    // Create and connect monitor and responder
    flMonitor     = new ("Monitor0", TX);
    flResponder   = new ("Responder0", TX);
      flResponder.rxDelayEn_wt            = MONITOR_DELAYEN_WT; 
      flResponder.rxDelayDisable_wt       = MONITOR_DELAYDIS_WT;
      flResponder.rxDelayLow              = MONITOR_DELAYLOW;
      flResponder.rxDelayHigh             = MONITOR_DELAYHIGH;
      flResponder.insideRxDelayEn_wt      = MONITOR_INSIDE_DELAYEN_WT; 
      flResponder.insideRxDelayDisable_wt = MONITOR_INSIDE_DELAYDIS_WT;
      flResponder.insideRxDelayLow        = MONITOR_INSIDE_DELAYLOW;
      flResponder.insideRxDelayHigh       = MONITOR_INSIDE_DELAYHIGH;    
      flMonitor.setCallbacks(scoreboard.monitorCbs);
      coverage.addFrameLinkInterfaceTx(MONITOR,"TXcoverage0");  
        
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
    for(int i=0; i<INPUT_COUNT; i++) 
      flDriver[i].setEnabled();
    flMonitor.setEnabled();
    flResponder.setEnabled();
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Enviroment
  task disableTestEnvironment();
    // Disable drivers
    #(1000*CLK_PERIOD);
    for(int i=0; i<INPUT_COUNT; i++)
      flDriver[i].setDisabled();
    // Disable monitor and responder
    #(12000*CLK_PERIOD);
    flMonitor.setDisabled();
    flResponder.setDisabled();
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
     
    for(int i=0; i<INPUT_COUNT; i++) begin  
      generator[i].setEnabled(TRANSACTION_COUNT);
    end

    // wait until all generators are disabled
    for(int i=0; i<INPUT_COUNT; i++) begin  
      wait (generator[i].enabled == 0);
    end
    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
    coverage.display();
  endtask: test1
  

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
    $write("INPUT_WIDTH:\t%1d\nOUTPUT_WIDTH:\t%1d\nINPUT_COUNT:\t%1d\nPARTS:\t%1d\nTICKET_PART:\t%1d\nTICKET_OFFSET:\t%1d\nTICKET_SIZE:\t%1d\nTICKET_FIFO_ITEMS:\t%1d\nINPUT_FIFO_ITEMS:\t%1d\nOUTPUT_FIFO_ITEMS:\t%1d\n",INPUT_WIDTH,OUTPUT_WIDTH,INPUT_COUNT,PARTS,TICKET_PART,TICKET_OFFSET,TICKET_SIZE,TICKET_FIFO_ITEMS,INPUT_FIFO_ITEMS,OUTPUT_FIFO_ITEMS);
    test1();       // Run Test 1
    
    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
 
    $stop();       // Stop testing
  end

endprogram

