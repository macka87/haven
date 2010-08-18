/*
 * test_8_64.sv: IB_TRANSFORMER automatic test
 * Copyright (C) 2008 CESNET
 * Author(s): Tomas Malek <tomalek@liberouter.org>
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
 * $Id :$
 *
 * TODO:
 *
 */

import test_pkg::*;            // Test constants and types
import ib_transaction_pkg::*;  // Internal Bus Transaction class
import ib_driver8_pkg::*;       // Internal Bus Driver class
import ib_driver64_pkg::*;       // Internal Bus Driver class
import ib_generator_pkg::*;    // Internal Bus Generator
import ib_monitor8_pkg::*;      // Internal Bus Monitor
import ib_monitor64_pkg::*;      // Internal Bus Monitor
import ib_scoreboard_pkg::*;   // Scoreboard Package
//import ib_coverage_pkg::*;     // Coverage


// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST_8_64 (
  input  logic  CLK,
  output logic  RESET,

  iIB64.tx      UP_IN,
  iIB64.rx      UP_OUT,
  iIB8.rx       DOWN_OUT,
  iIB8.tx       DOWN_IN
  );

  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------

  InternalBusDriver8    driverDown;            // Internal Bus Driver
  InternalBusDriver64   driverUp;              // Internal Bus Driver
  InternalBusGenerator  generatorDown;         // Transaction generator
  InternalBusGenerator  generatorUp;           // Transaction generator
  InternalBusMonitor8   monitorDown;           // Monitor 
  InternalBusMonitor64  monitorUp;             // Monitor 
  Scoreboard            scoreboard;            // Scoreboard
//  Coverage              coverage;            // Coverage
  tTransMbx             transMbxUp = new(1);   // Generator<->Driver Mailbox 
  tTransMbx             transMbxDown = new(1); // Generator<->Driver Mailbox
  InternalBusTransaction transaction;          // Transaction

  // --------------------------------------------------------------------------
  //                       Creating Enviroment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Enviroment
  task createEnviroment();
     // Create drivers    
     driverDown    = new(transMbxDown, DOWN_IN, 0);
     driverUp      = new(transMbxUp, UP_IN, 1);
     monitorDown   = new(DOWN_OUT, 0);
     monitorUp     = new(UP_OUT, 1);
     // Create generators
     generatorDown = new(transMbxDown);
     generatorUp   = new(transMbxUp);
     // Create scoreboard
     scoreboard = new;
     // Coverage class
//     coverage = new();
//     coverage.addInternalBusInterface(PORT0_UP,   "PORT0_UP");
//     coverage.addInternalBusInterface(PORT0_DOWN, "PORT0_DOWN");
//     coverage.addInternalBusInterface(PORT1_UP,   "PORT1_UP");
//     coverage.addInternalBusInterface(PORT1_DOWN, "PORT1_DOWN");
//     coverage.addInternalBusInterface(PORT2_UP,   "PORT2_UP");
//     coverage.addInternalBusInterface(PORT2_DOWN, "PORT2_DOWN");
//     coverage.addDriver(driver0, "Driver 0");
//     coverage.addDriver(driver1, "Driver 1");
//     coverage.addDriver(driver2, "Driver 2");

     // Set Callbacks
     driverDown.setCallbacks(scoreboard.driverCbs);
     driverUp.setCallbacks(scoreboard.driverCbs);
     monitorDown.setCallbacks(scoreboard.monitorCbs);
     monitorUp.setCallbacks(scoreboard.monitorCbs);
  endtask : createEnviroment

  // --------------------------------------------------------------------------
  //                       Test auxilarity procedures
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Resets Internal Bus Switch design
  task resetDesign();
    RESET=1;                       // Init Reset variable
    #cResetTime     RESET = 0;     // Deactivate reset after reset_time
    @(posedge CLK);
  endtask : resetDesign
  
  // --------------------------------------------------------------------------
  // Enable test Enviroment
  task enableTestEnviroment();
    // Enable Driver, Monitor, Coverage for each port
    driverDown.setEnabled();
    driverUp.setEnabled();
    monitorDown.setEnabled();
    monitorUp.setEnabled();
//    coverage.setEnabled();
  endtask : enableTestEnviroment

  // --------------------------------------------------------------------------
  // Disable test Enviroment
  task disableTestEnviroment(int clkCount = 0);
     // Disable drivers
     driverDown.setDisabled();
     driverUp.setDisabled();
     // Wait for finishing transactions
     #(clkCount*cClkPeriod);
     // Disable monitors
     monitorDown.setDisabled();
     monitorUp.setDisabled();
//     coverage.setDisabled();
  endtask : disableTestEnviroment

  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Test Case 1
  task test1();
     $write("\n\n############ TEST CASE 1 ############\n\n");
     // Enable Test enviroment
     disableTestEnviroment();     
     enableTestEnviroment();
     
     // Run generators
     generatorDown.setEnabled();
     generatorUp.setEnabled();
     
     // Send Hand-made transaction
     transaction = new;
     assert(transaction.randomize);
     transaction.localAddr = 32'h34ef3456;
     transaction.globalAddr = 64'h000000000bc9328d;
     transaction.transType = L2LR;
     transaction.length = 12'h01F;
     transaction.tag = 8'ha2;
     transaction.data = new[transaction.length];      
     for (integer i=0; i < transaction.data.size; i++) transaction.data[i] = i+1; 
     
     //transMbxDown.put(transaction); // uncomment for handmade transaction
     
     // Run test for x cloc cycles
     #(10000000*cClkPeriod); 

     // Disable generators
     generatorDown.setDisabled();
     generatorUp.setDisabled();

     // Disable Test Enviroment
     disableTestEnviroment(10000000);

     // Display Scoreboard
     scoreboard.scoreTable.display();
//     coverage.display();
  endtask: test1
  
  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
     // -------------------------------------
     // DESIGN ENVIROMENT
     // -------------------------------------
     createEnviroment(); // Create Test Enviroment

     // -------------------------------------
     // TESTING
     // -------------------------------------
 
     resetDesign(); // Reset design
     test1();       // Run Test 1

     // -------------------------------------
     // STOP TESTING
     // -------------------------------------

     $stop();       // Stop testing
  end



endprogram



