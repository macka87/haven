/*
 * test.sv: ib_endpoint automatic test
 * Copyright (C) 2009 CESNET
 * Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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
 * $Id: test.sv 8657 2009-06-04 10:57:57Z washek $
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import ib_common_pkg::*;
import ib_params_pkg::*;
import coverage_pkg::*;
import math_pkg::*;
import params::*;

import ib_memory_pkg::*;
import bm_monitor_pkg::*;
import scoreboard_pkg::*;
import endpoint_coverage_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input logic      CLK,
  output logic     RESET,
  iInternalBusRx.tb       IB_DOWN,
  iInternalBusTx.tb       IB_UP,
  iIbEndpointWrite.tb     WR,
  iIbEndpointRead.tb      RD,
  iInternalBusRx.tb       BM,
  iIbEndpointBMDone.tb    BM_DONE
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  
  parameter int DATA_WIDTH = G.DATA_WIDTH;
  parameter int DATA_WIDTH_B = DATA_WIDTH/8;
  parameter int LOG2DWB = log2(DATA_WIDTH_B);
  
  // IB Transaction
  InternalBusTransaction  ibBlueprint;
  // IB Generator
  Generator               ibGenerator;
  // IB Driver
  InternalBusDriver  #(DATA_WIDTH)    ibDriver;
  // IB Monitor
  InternalBusMonitor #(DATA_WIDTH)    ibMonitor;
  // Memory
  InternalBusMemory  #(G) memory;
  
  // BM Transaction
  InternalBusTransaction  bmBlueprint;
  // BM Generator
  Generator               bmGenerator;
  // BM Driver
  InternalBusDriver  #(DATA_WIDTH)  bmDriver;
  // BM Monitor
  IbBusMasterMonitor                    bmMonitor;
  
  // Scoreboard
  Scoreboard #(G) scoreboard;
  
  // Coverage
  IbEndpointCoverage #(G) coverage;
  
  // Transaction Counter
  TransCounter transCounter;
  
  // --------------------------------------------------------------------------
  //                            Create Environment
  // --------------------------------------------------------------------------

  // Create Test Environment
  task createEnvironment();
    int x;
    
    // Create IB generator
    ibGenerator = new("IB Generator", 0);
      ibBlueprint = new(parsTransIB[0]);
      ibBlueprint.addrAlignBits = (G.DATA_REORDER) ? 0 : LOG2DWB;
      ibGenerator.blueprint = ibBlueprint;
    
    // Create BM generator
    bmGenerator = new("BM Generator", 0);
      bmBlueprint = new(parsTransBM[0]);
      bmBlueprint.addrAlignBits = (G.DATA_REORDER) ? 0 : LOG2DWB;
      bmGenerator.blueprint = bmBlueprint;
    
    // Create IB driver
    ibDriver = new("IB Driver", IB_DOWN, ibGenerator.transMbx);
    
    // Create IB monitor
    ibMonitor = new("IB Monitor", IB_UP);
    
    // Create Memory
    memory = new("Memory", WR, RD);
    
    // Create BM driver
    bmDriver = new("BM Driver", BM, bmGenerator.transMbx);
    
    // Create BM monitor
    bmMonitor = new("BM Monitor", BM_DONE);
    
    // Create scoreboard
    scoreboard = new;
    
    // Create coverage class
    coverage = new(ibDriver, bmDriver, IB_DOWN, IB_UP, WR, RD, "");
    
    // Create coverage checking class
    transCounter = new();
    
    // Set scoreboard callbacks
    ibDriver.setCallbacks(scoreboard.driverCbs);
    ibMonitor.setCallbacks(scoreboard.monitorCbs);
    memory.setCallbacks(scoreboard.memoryCbs);
    
    bmDriver.setCallbacks(scoreboard.bmDriverCbs);
    bmMonitor.setCallbacks(scoreboard.bmMonitorCbs);
    
    // Set coverageChecking callbacks
    ibDriver.setCallbacks(transCounter);
    bmDriver.setCallbacks(transCounter);
    
    // Set random seeds
    x = $random(SEED);
    x = $urandom(2*SEED);
    
    ibGenerator.srandom(SEED);
    bmGenerator.srandom(7*SEED+1);
    
  endtask : createEnvironment

  // --------------------------------------------------------------------------
  //                       Test auxilarity procedures
  // --------------------------------------------------------------------------
  
  // --------------------------------------------------------------------------
  // Resets design
  task resetDesign();
    RESET=1;                 // Init Reset variable
    #RESET_TIME RESET = 0;   // Deactivate reset after reset_time
  endtask : resetDesign

  // --------------------------------------------------------------------------
  // Enable test Environment
  task enableEnvironment();
    ibDriver.setEnabled();
    ibMonitor.setEnabled();
    memory.setEnabled();
    if (G.BUS_MASTER_ENABLE) begin
      bmDriver.setEnabled();
      bmMonitor.setEnabled();
    end
    coverage.setEnabled();
  endtask : enableEnvironment
  
  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableEnvironment();
    ibDriver.setDisabled();
    ibMonitor.setDisabled();
    if (G.BUS_MASTER_ENABLE) begin
      bmDriver.setDisabled();
      bmMonitor.setDisabled();
    end
    memory.setDisabled();
    coverage.setDisabled();
  endtask : disableEnvironment
  
  // --------------------------------------------------------------------------
  // Disable drivers and wait for completion of all transactions
  task completeAndStop();
    int i;
    
    ibDriver.setDisabled();
    if (G.BUS_MASTER_ENABLE)
      bmDriver.setDisabled();
    
    //wait until drivers and monitors are not busy for 100 clk_periods
    i = 0;
    while (i < 100) begin
      if (ibMonitor.busy || bmMonitor.busy || memory.busy ||
          ibDriver.busy  || bmDriver.busy)
         i = 0;
      else
         i++;
      #CLK_PERIOD;
    end
    
    ibDriver.setEnabled();
    if (G.BUS_MASTER_ENABLE)
      bmDriver.setEnabled();
    
  endtask : completeAndStop
  
  
  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Standard random test
  task random_test();
  
    bit infinite_run = (TRANSACTION_COUNT < 0) ? 1 : 0; //Don't stop simulation
    int stop_count = 0, tmp;
    int ibTr, bmTr, ibDrv, bmDrv, ibMon, mem;
    
    // Enable test environment
    enableEnvironment();
    
    $display("\n*************** Standard random test ***************\n");
    
    while (1) begin
    
      // Set random parameters of transactions (type, length, ...)
      ibTr = $urandom_range($size(parsTransIB)-1);
      bmTr = $urandom_range($size(parsTransBM)-1);
      ibBlueprint.P = parsTransIB[ibTr];
      bmBlueprint.P = parsTransBM[bmTr];
      
      // Set random delays distribution for drivers and monitors
      ibDrv = $urandom_range($size(parsDrvD)-1);
      bmDrv = $urandom_range($size(parsDrvBmD)-1);
      ibMon = $urandom_range($size(parsMonD)-1);
      mem   = $urandom_range($size(parsMemD)-1);
      ibDriver.D  = parsDrvD[ibDrv];
      bmDriver.D  = parsDrvBmD[bmDrv];
      ibMonitor.D = parsMonD[ibMon];
      memory.D    = parsMemD[mem];
      
      // Run generators
      ibGenerator.setEnabled();
      if (G.BUS_MASTER_ENABLE)
        bmGenerator.setEnabled();
      
      // Wait until a random number of transactions is sent
      tmp = $urandom_range(1,200);
      stop_count += tmp;
      $write("Coverage: %5.2f. %5d transactions sent. Sending %3d more ",
              coverage.getCoverage(), transCounter.count, tmp);
      $display("(ibTr:%2d, bmTr:%2d, ibDrv:%2d, bmDrv:%2d, ibMon:%2d, mem:%2d)",
               ibTr, bmTr, ibDrv, bmDrv, ibMon, mem);
      
      while (transCounter.count < stop_count)
        #(CLK_PERIOD);
      
      ibGenerator.setDisabled();
      if (G.BUS_MASTER_ENABLE)
        bmGenerator.setDisabled();
      
      // Sometimes wait to completion of all transactions and check tables
      if ($urandom_range(0,4) == 0) begin
        
        // Stop generators and wait for all transactions
        $display("Transaction tables check.");
        completeAndStop();
        
        // Check that all transaction tables are empty
        assert (scoreboard.tablesEmpty()) else begin
          $display("Error: Some transaction hasn't been removed from table in scoreboard.");
          scoreboard.display();
          $stop();
          scoreboard.reset();
        end
        
        // Sometimes reset the design
        /*if ($urandom_range(0,2) == 0) begin
          $display("Reseting design.");
          //disableEnvironment();
          ibDriver.setDisabled();
          if (G.BUS_MASTER_ENABLE)
            bmDriver.setDisabled();
          resetDesign();
          //enableEnvironment();
          ibDriver.setEnabled();
          if (G.BUS_MASTER_ENABLE)
            bmDriver.setEnabled();
          // TODO reset funkce do dirveru a monitoru (a pamìti) aby se vždycky
          // všechno ukonèilo a na enableEnvironment zase spustilo.
        end*/
      end
      
      // If coverage reached 100% or number of sent transactions reached limit,
      // display tables and coverage infromation and pause simulation
      if (infinite_run == 0 && (transCounter.count >= TRANSACTION_COUNT
          || coverage.getCoverage() >= 100)) begin
        
        // Stop generators and wait for all transactions
        completeAndStop();
        
        // Display tables and coverage
        scoreboard.display();
        coverage.display();
        
        // End simulation
        $stop();
        // Don't stop, if we want to continue
        infinite_run = 1;
      end
      
    end // loop
    
    disableEnvironment();
    
  endtask: random_test
    
  
  
  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    
    createEnvironment();
    resetDesign();
    
    random_test();
    
  end

endprogram

