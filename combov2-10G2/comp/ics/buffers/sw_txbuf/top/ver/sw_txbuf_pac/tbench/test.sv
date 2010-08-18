/*
 * test.sv: SW_TX_BUFFER automatic test
 * Copyright (C) 2009 CESNET
 * Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
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
 * $Id: test.sv 8682 2009-06-05 18:25:38Z xsimko03 $
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import sv_txbufpac_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic     CLK,
  output logic     RESET,
  txBuffWrite.txbuff_write_tb BW,       // Write Interface
  txBuffRead.readBuff   BR[FLOWS],      // Read Interface
  txBuffRead.monitor    MONITOR[FLOWS]  // Monitor Interface
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  // Transaction
  txBuffTransaction                                                   buffBlueprint;
  // Generator                            
  Generator               generator;
  // Driver 
  txBuffPacDriver #(DRIVER0_DATA_WIDTH,DRIVER0_BLOCK_SIZE,DRIVER0_FLOWS,
                 DRIVER0_TOTAL_FLOW_SIZE)        bDriver;
  // Monitor
  FrameLinkMonitor #(MONITOR0_DATA_WIDTH,MONITOR0_BLOCK_SIZE,MONITOR0_FLOWS,
                     MONITOR0_TOTAL_FLOW_SIZE)  fMonitor[FLOWS];   
  // Responder
  FrameLinkResponder #(MONITOR0_DATA_WIDTH,MONITOR0_BLOCK_SIZE,MONITOR0_FLOWS,
                       MONITOR0_TOTAL_FLOW_SIZE)fResponder[FLOWS];   
  // Scoreboard
  Scoreboard  #(SCOREBOARD0_FLOWS,SCOREBOARD0_BEHAV)                  scoreboard;
  // Coverage
  Coverage #(DATA_WIDTH,TX_DATA_WIDTH,BLOCK_SIZE,FLOWS,TOTAL_FLOW_SIZE) coverage; 
  
  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createEnvironment();
    // Create generator
    generator = new("Generator0", 0);
    buffBlueprint = new;
    buffBlueprint.packetCount   = GENERATOR0_FL_PACKET_COUNT;
    buffBlueprint.flowCount     = GENERATOR0_FLOWS;
    buffBlueprint.packetSizeMax = GENERATOR0_FL_PACKET_SIZE_MAX;
    buffBlueprint.packetSizeMin = GENERATOR0_FL_PACKET_SIZE_MIN;
    generator.blueprint      = buffBlueprint;
    // Create scoreboard
    scoreboard = new;
    
    // Create driver    
    bDriver = new ("Driver0", generator.transMbx, BW);
    bDriver.fwDelayEn_wt             = DRIVER0_DELAYEN_WT; 
    bDriver.fwDelayDisable_wt        = DRIVER0_DELAYDIS_WT;
    bDriver.fwDelayLow               = DRIVER0_DELAYLOW;
    bDriver.fwDelayHigh              = DRIVER0_DELAYHIGH;
    bDriver.setCallbacks(scoreboard.driverCbs);
    
    // Create monitor
        
    fMonitor[0] = new ("Monitor0", 0, MONITOR[0]);
    /*fMonitor[1] = new ("Monitor1", 1, MONITOR[1]);
    fMonitor[2] = new ("Monitor2", 2, MONITOR[2]);
    fMonitor[3] = new ("Monitor3", 3, MONITOR[3]);
    fMonitor[4] = new ("Monitor4", 4, MONITOR[4]);
    fMonitor[5] = new ("Monitor5", 5, MONITOR[5]);
    fMonitor[6] = new ("Monitor6", 6, MONITOR[6]);
    fMonitor[7] = new ("Monitor7", 7, MONITOR[7]);*/
    // Create responder
    fResponder[0] = new ("Responder0", BR[0]);
    /*fResponder[1] = new ("Responder1", BR[1]);
    fResponder[2] = new ("Responder2", BR[2]);
    fResponder[3] = new ("Responder3", BR[3]);
    fResponder[4] = new ("Responder4", BR[4]);
    fResponder[5] = new ("Responder5", BR[5]);
    fResponder[6] = new ("Responder6", BR[6]);
    fResponder[7] = new ("Responder7", BR[7]);*/
        
    // Connect monitors and responders
    for(int i=0; i<FLOWS; i++) begin
      fResponder[i].rxDelayEn_wt            = MONITOR0_DELAYEN_WT; 
      fResponder[i].rxDelayDisable_wt       = MONITOR0_DELAYDIS_WT;
      fResponder[i].rxDelayLow              = MONITOR0_DELAYLOW;
      fResponder[i].rxDelayHigh             = MONITOR0_DELAYHIGH;
      fResponder[i].insideRxDelayEn_wt      = MONITOR0_INSIDE_DELAYEN_WT; 
      fResponder[i].insideRxDelayDisable_wt = MONITOR0_INSIDE_DELAYDIS_WT;
      fResponder[i].insideRxDelayLow        = MONITOR0_INSIDE_DELAYLOW;
      fResponder[i].insideRxDelayHigh       = MONITOR0_INSIDE_DELAYHIGH;
      fMonitor[i].setCallbacks(scoreboard.monitorCbs);
    end;
    
    // Coverage class
    coverage = new();
    coverage.addGeneralInterfaceWrite(BW,"BWcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[0],"BRcoverage");
    /*coverage.addGeneralInterfaceMonitor(MONITOR[1],"BRcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[2],"BRcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[3],"BRcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[4],"BRcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[5],"BRcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[6],"BRcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[7],"BRcoverage");*/

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
    bDriver.setEnabled();
    for(int i=0; i<FLOWS; i++) begin
      fMonitor[i].setEnabled();
      fResponder[i].setEnabled();
      end
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Enviroment
  task disableTestEnvironment();
    // Disable drivers
    #(1000*CLK_PERIOD);
    #(20000*CLK_PERIOD);
    for(int i=0; i<FLOWS; i++) begin
      fMonitor[i].setDisabled();
      fResponder[i].setDisabled();
    end
    bDriver.setDisabled();
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

     // Pokud je generator aktivni nic nedelej 
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

