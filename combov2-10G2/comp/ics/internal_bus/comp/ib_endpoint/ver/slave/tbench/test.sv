/*
 * test.sv: IB_ENDPOINT automatic test
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
 * $Id: test.sv 333 2007-09-05 20:07:59Z xkobie00 $
 *
 * TODO:
 *
 */
import test_pkg::*;            // Test constants and types
import ib_transaction_pkg::*;  // Internal Bus Transaction class
import ib_driver_pkg::*;       // Internal Bus Driver class
import ib_generator_pkg::*;    // Internal Bus Generator
import ib_monitor_pkg::*;      // Internal Bus Monitor
import ib_memory_pkg::*;       // Internal Bus Memory
import scoreboard_pkg::*;      // Scoreboard Package
//import ib_coverage_pkg::*;     // Coverage

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST(
  input logic                 CLK,
  output logic                RESET,
  iIbEndpointWrite64.user     WR,
  iIbEndpointRead64s.user     RD,
  iInternalBusLink.rx         IB_DOWN,
  iInternalBusLink.tx         IB_UP
  );
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  InternalBusDriver    driver;            // Internal Bus Driver
  InternalBusGenerator generator;         // Internal Bus Generator
  InternalBusMonitor   monitor;           // Internal Bus Monitor
  InternalBusMemory    memory;            // Internal Bus Memory
  tTransMbx            transMbx = new(1); // Transaction MailBox
  Scoreboard           scoreboard;        // Scoreboard
  
  // --------------------------------------------------------------------------
  //                       Creating Enviroment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Enviroment
  task createEnviroment();
     driver     = new(transMbx, IB_DOWN, 0); // Create Driver
     monitor    = new(IB_UP, 0);             // Create Monitor
     generator  = new(transMbx);             // Create generators
     memory     = new(WR, RD, 0);            // Create Memory
	 scoreboard = new;                       // Crate Scoreboard
	 // Set Callbacks
	 driver.setCallbacks(scoreboard.driverCbs);
	 monitor.setCallbacks(scoreboard.monitorCbs);
	 memory.setCallbacks(scoreboard.memoryCbs);
	 
  endtask : createEnviroment


  // --------------------------------------------------------------------------
  //                       Test auxilarity procedures
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Resets Internal Bus Switch design
  task resetDesign();
    RESET=1;                       // Init Reset variable
    #cResetTime     RESET = 0;     // Deactivate reset after reset_time
  endtask : resetDesign


  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Test Case 1
  task test1();
     $write("\n\n############ TEST CASE 1 ############\n\n");

     // Enable Test enviroment
     driver.setEnabled();
     monitor.setEnabled();
     memory.setEnabled();

     // Run generators
     generator.setEnabled();
     
     // Run test for that much clock cycles
     #(10000*cClkPeriod); 

     // Disable generators
     generator.setDisabled();
     driver.setDisabled();

     // Wait for finishing transactions
     #(1000*cClkPeriod);
     monitor.setDisabled();

	 scoreboard.memoryTransactionTable.display();
    scoreboard.ibTransactionTable.display();


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

endprogram : TEST
