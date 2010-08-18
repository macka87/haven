/*
 * test.sv: ib_switch automatic test
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
 * $Id: test.sv 12297 2009-12-16 18:17:27Z washek $
 *
 * TODO:
 *
 */

import math_pkg::*;
import sv_common_pkg::*;
import ib_common_pkg::*;
import ib_params_pkg::*;
import scoreboard_pkg::*;
import switch_coverage_pkg::*;
import switch_generator_pkg::*;
import params::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input logic      CLK,
  output logic     RESET,
  iInternalBusRx.tb    UP_RX,
  iInternalBusTx.tb    UP_TX,
  iInternalBusRx.tb    D1_RX,
  iInternalBusTx.tb    D1_TX,
  iInternalBusRx.tb    D2_RX,
  iInternalBusTx.tb    D2_TX
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  
  parameter int DATA_WIDTH = G.DATA_WIDTH;
  parameter int DATA_WIDTH_B = DATA_WIDTH/8;
  parameter int LOG2DWB = log2(DATA_WIDTH_B);
  
  // Transaction
  InternalBusTransaction  blueprint0;
  InternalBusTransaction  blueprint1;
  InternalBusTransaction  blueprint2;
  // Generators
  Generator  generator0;
  Generator  generator1;
  Generator  generator2;
  SwitchGenerator #(G) switchGen0;
  SwitchGenerator #(G) switchGen1;
  SwitchGenerator #(G) switchGen2;
  // Drivers
  InternalBusDriver   #(DATA_WIDTH) driver0;
  InternalBusDriver   #(DATA_WIDTH) driver1;
  InternalBusDriver   #(DATA_WIDTH) driver2;
  // Monitors
  InternalBusMonitor  #(DATA_WIDTH) monitor0;
  InternalBusMonitor  #(DATA_WIDTH) monitor1;
  InternalBusMonitor  #(DATA_WIDTH) monitor2;
  // Scoreboard
  Scoreboard #(G) scoreboard;
  // Coverage
  IbSwitchCoverage #(G) coverage; 
  // Transaction Counter
  TransCounter transCounter;
  
  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // Create Test Environment
  task createEnvironment();
    int x;
    
    // Create generators
    generator0  = new("Generator 0", 0);
      blueprint0 = new(parsTransUp[0]);
      generator0.blueprint = blueprint0;
    
    generator1  = new("Generator 1", 0);
      blueprint1 = new(parsTransDown[0]);
      generator1.blueprint = blueprint1;
    
    generator2  = new("Generator 2", 0);
      blueprint2 = new(parsTransDown[0]);
      generator2.blueprint = blueprint2;
    
    switchGen0 = new("SwitchGenerator 0", 0, generator0.transMbx);
    switchGen1 = new("SwitchGenerator 1", 0, generator1.transMbx);
    switchGen2 = new("SwitchGenerator 2", 0, generator2.transMbx);
    switchGen0.blueprint = blueprint0;
    switchGen1.blueprint = blueprint1;
    switchGen2.blueprint = blueprint2;
    
    // Create drivers    
    driver0 = new ("Driver 0", UP_RX, generator0.transMbx);
    driver1 = new ("Driver 1", D1_RX, generator1.transMbx);
    driver2 = new ("Driver 2", D2_RX, generator2.transMbx);
    
    // Create monitor
    monitor0 = new ("Monitor 0", UP_TX);
    monitor1 = new ("Monitor 1", D1_TX);
    monitor2 = new ("Monitor 2", D2_TX);
    
    // Create scoreboard
    scoreboard = new;
    
    // Coverage class
    coverage = new(driver0,driver1,driver2,UP_RX,UP_TX,D1_RX,D1_TX,D2_RX,D2_TX);
    
    // Transaction counter
    transCounter = new;
    
    // Set scoreboard callbacks
    driver0.setCallbacks(scoreboard.driver0Cbs);
    driver1.setCallbacks(scoreboard.driver1Cbs);
    driver2.setCallbacks(scoreboard.driver2Cbs);
    monitor0.setCallbacks(scoreboard.monitor0Cbs);
    monitor1.setCallbacks(scoreboard.monitor1Cbs);
    monitor2.setCallbacks(scoreboard.monitor2Cbs);
    
    // Set counter callbacks
    driver0.setCallbacks(transCounter);
    driver1.setCallbacks(transCounter);
    driver2.setCallbacks(transCounter);
    
    // Set random seeds
    x = $urandom(SEED);
    x = $random(2*SEED);
    generator0.srandom(SEED+3);
    generator1.srandom(2*SEED+1);
    generator2.srandom(3*SEED+5);
    switchGen0.srandom(SEED+102);
    switchGen1.srandom(SEED+203);
    switchGen2.srandom(SEED+304);
    
  endtask : createEnvironment

  // --------------------------------------------------------------------------
  //                       Test auxilarity procedures
  // --------------------------------------------------------------------------
  
  // --------------------------------------------------------------------------
  // Resets design
  task resetDesign();
    RESET=1;                     // Init Reset variable
    #RESET_TIME   RESET = 0;     // Deactivate reset after reset_time
  endtask : resetDesign

  // --------------------------------------------------------------------------
  // Enable test Environment
  task enableEnvironment();
    monitor0.setEnabled();
    monitor1.setEnabled();
    monitor2.setEnabled();
    driver0.setEnabled();
    driver1.setEnabled();
    driver2.setEnabled();
    coverage.setEnabled();
  endtask : enableEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableEnvironment();
     driver0.setDisabled();
     driver1.setDisabled();
     driver2.setDisabled();
     monitor0.setDisabled();
     monitor1.setDisabled();
     monitor2.setDisabled();
     coverage.setDisabled();
  endtask : disableEnvironment

  // --------------------------------------------------------------------------
  // Disable drivers and wait for completion of all transactions
  task completeAndStop();
    int i;
    
    driver0.setDisabled();
    driver1.setDisabled();
    driver2.setDisabled();
    
    //wait until drivers and monitors are not busy for 100 clk_periods
    i = 0;
    while (i < 100) begin
      if (monitor0.busy || monitor1.busy || monitor2.busy ||
          driver0.busy  || driver1.busy  || driver2.busy)
         i = 0;
      else
         i++;
      #CLK_PERIOD;
    end
    
    driver0.setEnabled();
    driver1.setEnabled();
    driver2.setEnabled();
    
  endtask : completeAndStop

  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Standard test
  task random_test();
    
    bit infinite_run = (TRANSACTION_COUNT < 0) ? 1 : 0; //Don't stop simulation
    int stop_count = 0, tmp;
    int tr0, tr1, tr2, drv0, drv1, drv2, mon0, mon1, mon2;
    
    // Enable test environment
    enableEnvironment();
    
    $display("\n*************** Standard semi-random test ***************\n");
    
    while (1) begin
      
      // Set random parameters of transactions (type, length, ...)
      tr0 = $urandom_range($size(parsTransUp)-1);
      tr1 = $urandom_range($size(parsTransDown)-1);
      tr2 = $urandom_range($size(parsTransDown)-1);
      blueprint0.P = parsTransUp[tr0];
      blueprint1.P = parsTransDown[tr1];
      blueprint2.P = parsTransDown[tr2];
      
      // Set random delays distribution for drivers and monitors
      drv0 = $urandom_range($size(parsDrvD)-1);
      drv1 = $urandom_range($size(parsDrvD)-1);
      drv2 = $urandom_range($size(parsDrvD)-1);
      mon0 = $urandom_range($size(parsMonD)-1);
      mon1 = $urandom_range($size(parsMonD)-1);
      mon2 = $urandom_range($size(parsMonD)-1);
      driver0.D  = parsDrvD[drv0];
      driver1.D  = parsDrvD[drv1];
      driver2.D  = parsDrvD[drv2];
      monitor0.D = parsMonD[mon0];
      monitor1.D = parsMonD[mon1];
      monitor2.D = parsMonD[mon2];
      
      // Run generators
      generator0.setEnabled();
      generator1.setEnabled();
      generator2.setEnabled();
      switchGen0.setEnabled();
      switchGen1.setEnabled();
      switchGen2.setEnabled();
      
      // Wait until a random number of transactions is sent
      tmp = $urandom_range(1,200);
      stop_count += tmp;
      $write("Coverage: %5.2f. %5d transactions sent. Sending %3d more ",
              coverage.getCoverage(), transCounter.count, tmp);
      $write("(tr0:%2d, tr1:%2d, tr2:%2d, drv0:%2d, drv1:%2d, drv2:%2d, ",
              tr0, tr1, tr2, drv0, drv1, drv2); 
      $write("mon0:%2d, mon1:%2d, mon2:%2d)\n", mon0, mon1, mon2);
      
      while (transCounter.count < stop_count)
        #(CLK_PERIOD);
      
      generator0.setDisabled();
      generator1.setDisabled();
      generator2.setDisabled();
      switchGen0.setDisabled();
      switchGen1.setDisabled();
      switchGen2.setDisabled();
      
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
          driver0.setDisabled();
          driver1.setDisabled();
          driver2.setDisabled();
          resetDesign();
          //enableEnvironment();
          driver0.setEnabled();
          driver1.setEnabled();
          driver2.setEnabled();
          // TODO reset funkce do dirveru a monitoru (a pamìti) aby se v¾dycky
          // v¹echno ukonèilo a na enableEnvironment zase spustilo.
        end*/
      end
      
      // If coverage reached 100% or number of sent transactions reached limit
      // display tables and coverage infromation and break simulation
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
  //My test
  task my_test();
    
    driver0.D  = parsDrvD[0];
    driver1.D  = parsDrvD[0];
    driver2.D  = parsDrvD[0];
    monitor0.D = parsMonD[0];
    monitor1.D = parsMonD[0];
    monitor2.D = parsMonD[0];
    
    // Enable test environment
    monitor0.setEnabled();
    monitor1.setEnabled();
    monitor2.setEnabled();
    
    driver0.setEnabled();
    
    blueprint0.P = parsTransUp[0];
    generator0.setEnabled(1);
    
    while (transCounter.count < 1)
        #(CLK_PERIOD);
    
    //generator0.setDisabled();
    //driver0.setDisabled();
    
    blueprint1.P = parsTransDown[0];
    generator1.setEnabled(1);
    driver1.setEnabled();
    
    while (transCounter.count < 2)
        #(CLK_PERIOD);
    
    //generator1.setDisabled();
    driver1.setDisabled();
    
    blueprint0.P = parsTransUp[1];
    generator0.setEnabled(1);
    driver0.setEnabled();
    
    while (transCounter.count < 3)
        #(CLK_PERIOD);
    
    //generator0.setDisabled();
    driver0.setDisabled();
    
    blueprint2.P = parsTransDown[1];
    generator2.setEnabled(1);
    driver2.setEnabled();
    
    while (transCounter.count < 4)
        #(CLK_PERIOD);
    
    #(100*CLK_PERIOD);
    
    disableEnvironment();
    
    $stop();
    
  endtask: my_test
  
  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    
    createEnvironment();
    resetDesign();
    
    random_test();
    
    //my_test();
    
  end

endprogram

