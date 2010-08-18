/*
 * test.sv: ib_transformer automatic test
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
import params::*;
import scoreboard_pkg::*;
import transformer_coverage_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input logic      CLK,
  output logic     RESET,
  iInternalBusRx.tb    UP_RX,
  iInternalBusTx.tb    UP_TX,
  iInternalBusRx.tb    DOWN_RX,
  iInternalBusTx.tb    DOWN_TX
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
 
  // Transaction
  InternalBusTransaction  upBlueprint;
  InternalBusTransaction  downBlueprint;
  // Generators
  Generator               upGenerator;
  Generator               downGenerator;
  // Drivers
  InternalBusDriver  #(G.UP_DATA_WIDTH)   upDriver;
  InternalBusDriver  #(G.DOWN_DATA_WIDTH) downDriver;
  // Monitors
  InternalBusMonitor #(G.UP_DATA_WIDTH)   upMonitor;
  InternalBusMonitor #(G.DOWN_DATA_WIDTH) downMonitor;
  // Scoreboard
  Scoreboard  scoreboard;
  // Coverage
  IbTransformerCoverage #(G.UP_DATA_WIDTH, G.DOWN_DATA_WIDTH) coverage; 
  // Transaction Counter
  TransCounter transCounter;
    
  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createEnvironment();
    int x;
    
    // Create generators
    upGenerator   = new("UP Generator", 0);
      upBlueprint = new(parsTransUp[0]);
      upGenerator.blueprint = upBlueprint;
    downGenerator = new("DOWN Generator", 0);
      downBlueprint = new(parsTransDown[0]);
      downGenerator.blueprint = downBlueprint;

    // Create drivers    
    upDriver   = new ("UP Driver",   UP_RX,   upGenerator.transMbx);
    downDriver = new ("DOWN Driver", DOWN_RX, downGenerator.transMbx);
    
    // Create monitor
    upMonitor   = new ("UP Monitor",   UP_TX);
    downMonitor = new ("DOWN Monitor", DOWN_TX);
    
    // Create scoreboard
    scoreboard = new;
    
    // Coverage class
    coverage = new(upDriver, downDriver, UP_RX, UP_TX, DOWN_RX, DOWN_TX);
    
    // Transaction counter
    transCounter = new;
    
    // Set Callbacks
    upDriver.setCallbacks(scoreboard.upDriverCbs);
    downDriver.setCallbacks(scoreboard.downDriverCbs);
    upMonitor.setCallbacks(scoreboard.upMonitorCbs);
    downMonitor.setCallbacks(scoreboard.downMonitorCbs);
    
    upDriver.setCallbacks(transCounter);
    downDriver.setCallbacks(transCounter);
    
    // Set random seeds
    x = $urandom(SEED);
    x = $random(2*SEED);
    upGenerator.srandom(SEED+101);
    downGenerator.srandom(2*SEED+202);
    
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
    upMonitor.setEnabled();
    downMonitor.setEnabled();
    upDriver.setEnabled();
    downDriver.setEnabled();
    coverage.setEnabled();
  endtask : enableEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableEnvironment();
    upMonitor.setDisabled();
    downMonitor.setDisabled();
    upDriver.setDisabled();
    downDriver.setDisabled();
    coverage.setDisabled();
  endtask : disableEnvironment
  
  // --------------------------------------------------------------------------
  // Disable drivers and wait for completion of all transactions
  task completeAndStop();
    int i;
    
    upDriver.setDisabled();
    downDriver.setDisabled();
    
    //wait until drivers and monitors are not busy for 100 clk_periods
    i = 0;
    while (i < 100) begin
      if (upMonitor.busy || downMonitor.busy ||
          upDriver.busy  || downDriver.busy )
         i = 0;
      else
         i++;
      #CLK_PERIOD;
    end
    
    upDriver.setEnabled();
    downDriver.setEnabled();
    
  endtask : completeAndStop
  
  
  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Standard test
  task random_test();
    
    bit infinite_run = (TRANSACTION_COUNT < 0) ? 1 : 0; //Don't stop simulation
    int stop_count = 0, tmp;
    int trUp, trDown, drvUp, drvDown, monUp, monDown;
    
    // Enable test environment
    enableEnvironment();
    
    $display("\n*************** Standard random test ***************\n");
    
    while (1) begin
      
      // Set random parameters of transactions (type, length, ...)
      trUp   = $urandom_range($size(parsTransUp)-1);
      trDown = $urandom_range($size(parsTransDown)-1);
      upBlueprint.P   = parsTransUp[trUp];
      downBlueprint.P = parsTransDown[trDown];
      
      // Set random delays distribution for drivers and monitors
      drvUp   = $urandom_range($size(parsDrvD)-1);
      drvDown = $urandom_range($size(parsDrvD)-1);
      monUp   = $urandom_range($size(parsMonD)-1);
      monDown = $urandom_range($size(parsMonD)-1);
      upDriver.D    = parsDrvD[drvUp];
      downDriver.D  = parsDrvD[drvDown];
      upMonitor.D   = parsMonD[monUp];
      downMonitor.D = parsMonD[monDown];
      
      // Run generators
      upGenerator.setEnabled();
      downGenerator.setEnabled();
      
      // Wait until a random number of transactions is sent
      tmp = $urandom_range(1,200);
      stop_count += tmp;
      $write("Coverage: %5.2f. %5d transactions sent. Sending %3d more ",
              coverage.getCoverage(), transCounter.count, tmp);
      $write("(trUp:%2d, trDown:%2d, drvUp:%2d, drvDown:%2d, ",
              trUp, trDown, drvUp, drvDown); 
      $write("monUp:%2d, monDown:%2d)\n", monUp, monDown);
      
      while (transCounter.count < stop_count)
        #(CLK_PERIOD);
      
      upGenerator.setDisabled();
      downGenerator.setDisabled();
      
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
          upDriver.setDisabled();
          downdriver.setDisabled();
          resetDesign();
          //enableEnvironment();
          upDriver.setEnabled();
          downDriver.setEnabled();
          // TODO reset funkce do dirveru a monitoru (a pamìti) aby se vždycky
          // všechno ukonèilo a na enableEnvironment zase spustilo.
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
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    
    createEnvironment();
    resetDesign();
    
    random_test();
    
  end

endprogram

