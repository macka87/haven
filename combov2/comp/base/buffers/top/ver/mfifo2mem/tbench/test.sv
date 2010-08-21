/*
 * test.sv: Automatic test
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
 * $Id: test.sv 13523 2010-04-15 13:32:20Z xsanta06 $
 *
 * TODO:
 *
 */

import sv_buffer_pkg::*; 
import test_pkg::*;
import sv_common_pkg::*;


// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic           CLK,
  output logic           RESET,  
  iNFifoTx.fifo_write_tb FW,
  iMemRead.tb            MR
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  
  // Transaction
  BufferTransaction                                              buffBlueprint;                  
  // Generator 
  Generator                                                      generator; 
  // Driver 
  FifoDriver #(DRIVER0_DATA_WIDTH,DRIVER0_FLOWS,DRIVER0_BLOCK_SIZE,
                 DRIVER0_LUT_MEMORY, 0)                          fDriver;
  // Monitor
  MemMonitorNew #(MONITOR0_DATA_WIDTH,MONITOR0_FLOWS,MONITOR0_BLOCK_SIZE,
                 MONITOR0_LUT_MEMORY, MONITOR0_OUTPUT_REG)
                                                                 memMonitor;   
  // Scoreboard
  Scoreboard                                                     scoreboard;
  // Coverage
  Coverage #(DATA_WIDTH,FLOWS,BLOCK_SIZE,LUT_MEMORY, 0)        coverage;  
  
  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------  
  // Create Test Environment
  task createEnvironment();
    // Create generator
    generator = new("Generator0", 0);
    buffBlueprint = new;
    buffBlueprint.dataSize   = GENERATOR0_DATA_SIZE;
    buffBlueprint.flowCount  = GENERATOR0_FLOW_COUNT;
    generator.blueprint      = buffBlueprint;
   
    // Create scoreboard
    scoreboard = new;
    
    // Coverage class
    coverage = new();
      
    // Create and connect driver 
    fDriver = new ("Driver0", generator.transMbx, FW);
    fDriver.fwDelayEn_wt             = DRIVER0_DELAYEN_WT; 
    fDriver.fwDelayDisable_wt        = DRIVER0_DELAYDIS_WT;
    fDriver.fwDelayLow               = DRIVER0_DELAYLOW;
    fDriver.fwDelayHigh              = DRIVER0_DELAYHIGH;
    fDriver.setCallbacks(scoreboard.driverCbs);
    coverage.addGeneralInterfaceWrite(FW,"MFIFO Coverage");
    
    // Create and connect monitor
    memMonitor = new ("Monitor", MR);
      memMonitor.readDelayEn_wt             = MONITOR0_DELAYEN_WT; 
      memMonitor.readDelayDisable_wt        = MONITOR0_DELAYDIS_WT;   
      memMonitor.pipeDelayEn_wt             = MONITOR0_PIPEEN_WT; 
      memMonitor.pipeDelayDisable_wt        = MONITOR0_PIPEDIS_WT;   
    memMonitor.setCallbacks(scoreboard.monitorCbs);
    coverage.addGeneralInterfaceMonitor(MR,"MEM Coverage");

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
    fDriver.setEnabled();
    memMonitor.setEnabled();
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Enviroment
  task disableTestEnvironment();
    int i=0;

    // Disable drivers
    #(100*CLK_PERIOD);
    fDriver.setDisabled();

    // Wait while all transaction are received
    finishReceiving();

    memMonitor.setDisabled();
    coverage.setDisabled();
  endtask : disableTestEnvironment

  // --------------------------------------------------------------------------
  // Finish receiving
  task finishReceiving();
    int i;

    i = 0;
    // Check if monitor is not receiving transaction for 100 CLK_PERIODs
    while (i<100) begin
      if (memMonitor.busy)
        i = 0;
      else i++;
      #(CLK_PERIOD); 
    end
  endtask : finishReceiving
  
  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Test Case 1
  task test1();
    $write("\n\n############ TEST CASE 1 ############\n\n");
    $write("## Part 1: Delays on interfaces from test_pkg.\n");
    // Enable Test enviroment
    enableTestEnvironment();
    // Run generators 
    generator.setEnabled(TRANSACTION_COUNT);
    
    // Wait while generator generates transactions 
    while (generator.enabled)
      #(CLK_PERIOD);

    // Wait while all transaction are received
    finishReceiving();
    // Display Scoreboard
    scoreboard.display();

    // -----
    $write("\n## Part 2: No delays on interfaces.\n");
    // No delays on input interface
    fDriver.fwDelayEn_wt             = 0; 
    fDriver.fwDelayDisable_wt        = 1;

    // No delays on output interface
    memMonitor.readDelayEn_wt        = 0; 
    memMonitor.readDelayDisable_wt   = 1;   
    memMonitor.pipeDelayEn_wt        = 0; 
    memMonitor.pipeDelayDisable_wt   = 1;   

    // Run generators 
    @(fDriver.f_w.fifo_write_cb);         // Synchronize driver 
    generator.setEnabled(TRANSACTION_COUNT);
    
    // Wait while generator generates transactions 
    while (generator.enabled)
      #(CLK_PERIOD);

    // Wait while all transaction are received
    finishReceiving();
    // Display Scoreboard
    scoreboard.display();

    // -----
    $write("\n## Part 3: Delays on output interface only.\n");
    // No delays on input interface
    fDriver.fwDelayEn_wt             = 0; 
    fDriver.fwDelayDisable_wt        = 1;

    // Delays on output interface
    memMonitor.readDelayEn_wt        = 1; 
    memMonitor.readDelayDisable_wt   = 2;   
    memMonitor.pipeDelayEn_wt        = 1; 
    memMonitor.pipeDelayDisable_wt   = 2;   

    // Run generators 
    @(fDriver.f_w.fifo_write_cb);          // Synchronize driver 
    generator.setEnabled(TRANSACTION_COUNT);
    
    // Wait while generator generates transactions 
    while (generator.enabled)
      #(CLK_PERIOD);

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


