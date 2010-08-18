/*
 * test.sv: IB_SWITCH automatic test
 * Copyright (C) 2008 CESNET
 * Author(s): Petr Kobiersky <kobiersky@liberouter.org>
 *            Tomas Malek <tomalek@liberouter.org>
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
 * $Id: test.sv 1364 2008-02-18 15:23:10Z tomalek $
 *
 * TODO:
 *
 */

import test_pkg::*;            // Test constants and types
import ib_transaction_pkg::*;  // Internal Bus Transaction class
import ib_driver_pkg::*;       // Internal Bus Driver class
import ib_generator_pkg::*;    // Internal Bus Generator
import ib_monitor_pkg::*;      // Internal Bus Monitor
import ib_scoreboard_pkg::*;   // Scoreboard Package
//import ib_coverage_pkg::*;     // Coverage


// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic  CLK,
  output logic  RESET,
  iIB.tx        PORT0_DOWN,
  iIB.rx        PORT0_UP,
  iIB.rx        PORT1_DOWN,
  iIB.tx        PORT1_UP,
  iIB.rx        PORT2_DOWN,
  iIB.tx        PORT2_UP
  );

  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------

  InternalBusDriver     driver0;            // Internal Bus Driver 0
  InternalBusDriver     driver1;            // Internal Bus Driver 1
  InternalBusDriver     driver2;            // Internal Bus Driver 2
  InternalBusGenerator  generator0;         // Transaction generator 0
  InternalBusGenerator  generator1;         // Transaction generator 0
  InternalBusGenerator  generator2;         // Transaction generator 0
  InternalBusMonitor    monitor0;           // Monitor 0
  InternalBusMonitor    monitor1;           // Monitor 1
  InternalBusMonitor    monitor2;           // Monitor 2
  Scoreboard            scoreboard;         // Scoreboard
//  Coverage              coverage;           // Coverage
  tTransMbx             transMbx0 = new(1); // Generator<->Driver Mailbox 0
  tTransMbx             transMbx1 = new(1); // Generator<->Driver Mailbox 1
  tTransMbx             transMbx2 = new(1); // Generator<->Driver Mailbox 2
  InternalBusTransaction transaction;       // Transaction

  // --------------------------------------------------------------------------
  //                       Creating Enviroment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Enviroment
  task createEnviroment();
     // Create drivers    
     driver0    = new(transMbx0, PORT0_DOWN, 0);
     driver1    = new(transMbx1, PORT1_UP, 1);
     driver2    = new(transMbx2, PORT2_UP, 2);
     monitor0   = new(PORT0_UP, 0);
     monitor1   = new(PORT1_DOWN, 1);
     monitor2   = new(PORT2_DOWN, 2);
     // Create generators
     generator0 = new(transMbx0);
     generator1 = new(transMbx1);
     generator2 = new(transMbx2);
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
     driver0.setCallbacks(scoreboard.driverCbs);
     driver1.setCallbacks(scoreboard.driverCbs);
     driver2.setCallbacks(scoreboard.driverCbs);
     monitor0.setCallbacks(scoreboard.monitorCbs);
     monitor1.setCallbacks(scoreboard.monitorCbs);
     monitor2.setCallbacks(scoreboard.monitorCbs);
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
    driver0.setEnabled();
    driver1.setEnabled();
    driver2.setEnabled();
    monitor0.setEnabled();
    monitor1.setEnabled();
    monitor2.setEnabled();
//    coverage.setEnabled();
  endtask : enableTestEnviroment

  // --------------------------------------------------------------------------
  // Disable test Enviroment
  task disableTestEnviroment(int clkCount = 0);
     // Disable drivers
     driver0.setDisabled();
     driver1.setDisabled();
     driver2.setDisabled();
     // Wait for finishing transactions
     #(clkCount*cClkPeriod);
     // Disable monitors
     monitor0.setDisabled();
     monitor1.setDisabled();
     monitor2.setDisabled();
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
     generator0.setEnabled();
     generator1.setEnabled();
     generator2.setEnabled();
     
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
     
     //transMbx0.put(transaction); // uncomment for handmade transaction
     
     // Run test for x cloc cycles
     #(500000*cClkPeriod); 

     // Disable generators
     generator0.setDisabled();
     generator1.setDisabled();
     generator2.setDisabled();

     // Disable Test Enviroment
     disableTestEnviroment(100000);

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



