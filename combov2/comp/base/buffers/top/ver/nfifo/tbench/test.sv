/*
 * test.sv: Automatic test
 * Copyright (C) 2008 CESNET
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
 * $Id: test.sv 7813 2009-03-27 14:11:00Z xsanta06 $
 *
 * TODO:
 *
 */

import sv_buffer_pkg::*; 
import test_pkg::*;
import sv_common_pkg::*;
import math_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic           CLK,
  output logic           RESET,  
  iNFifoTx.fifo_write_tb FW,
  iNFifoRx.fifo_read_tb  FR ,
  iNFifoRx.fifo_monitor  MONITOR
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  // AK MA KOMPONENTA VIAC DRIVEROV ALEBO MONITOROV TREBA ICH NA TOMTO MIESTE DEKLAROVAT A V TASKU
  // CREATEENVIRONMENT INSTANCIOVAT
  
  // Transaction
  BufferTransaction                                                   buffBlueprint;                  
  // Generator 
  Generator                                                           generator; 
  // Driver 
  FifoDriver #(DRIVER0_DATA_WIDTH,DRIVER0_FLOWS,DRIVER0_BLOCK_SIZE,
                 DRIVER0_LUT_MEMORY, DRIVER0_GLOB_STATE)              fDriver;
  // Monitor
  FifoMonitor #(MONITOR0_DATA_WIDTH,MONITOR0_FLOWS,MONITOR0_BLOCK_SIZE,
                 MONITOR0_LUT_MEMORY, MONITOR0_OUTPUT_REG, MONITOR0_GLOB_STATE)
                                                                      fMonitor;   
  // Responder
  FifoResponder #(MONITOR0_DATA_WIDTH,MONITOR0_FLOWS,MONITOR0_BLOCK_SIZE,
                 MONITOR0_LUT_MEMORY, MONITOR0_GLOB_STATE, MONITOR0_OUTPUT_REG)            
                                                                      fResponder;  
  // Scoreboard
  Scoreboard                                                          scoreboard;
  // Coverage
  Coverage #(DATA_WIDTH,FLOWS,BLOCK_SIZE,LUT_MEMORY,GLOB_STATE)       coverage;  
  
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
    
    // Create driver    
    fDriver = new ("Driver0", generator.transMbx, FW);
    fDriver.fwDelayEn_wt             = DRIVER0_DELAYEN_WT; 
    fDriver.fwDelayDisable_wt        = DRIVER0_DELAYDIS_WT;
    fDriver.fwDelayLow               = DRIVER0_DELAYLOW;
    fDriver.fwDelayHigh              = DRIVER0_DELAYHIGH;
    fDriver.setCallbacks(scoreboard.driverCbs);
  
    // Create monitor
    fMonitor = new ("Monitor", MONITOR);
    
    // Create responder
    fResponder = new ("Responder", FR);
        
    // Connect monitors and responders
    fResponder.frDelayEn_wt               = MONITOR0_DELAYEN_WT; 
    fResponder.frDelayDisable_wt          = MONITOR0_DELAYDIS_WT;   
    fResponder.frDelayLow                 = MONITOR0_DELAYLOW;
    fResponder.frDelayHigh                = MONITOR0_DELAYHIGH;
    fResponder.pipeDelayEn_wt             = MONITOR0_PIPEDELAYEN_WT; 
    fResponder.pipeDelayDisable_wt        = MONITOR0_PIPEDELAYDIS_WT;   
    fResponder.pipeDelayLow               = MONITOR0_PIPEDELAYLOW;
    fResponder.pipeDelayHigh              = MONITOR0_PIPEDELAYHIGH;
    fMonitor.setCallbacks(scoreboard.monitorCbs);
    
    // Coverage class
    coverage = new();
    coverage.addGeneralInterfaceWrite(FW,"FWcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR,"FRcoverage");
    
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
    fMonitor.setEnabled();
    fResponder.setEnabled(); // do not switch it off - generates BLOCK_ADDR
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Enviroment
  task disableTestEnvironment();
     // Disable drivers
    #(1000*CLK_PERIOD);
    fDriver.setDisabled();
    #(2000*CLK_PERIOD);
    // Disable monitor, responder and coverage
    fMonitor.setDisabled();
    fResponder.setDisabled();
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
    
    $write("\n\n############ GENERICS ############\n\n");
    $write("DATA_WIDTH:\t%1d\nFLOWS:\t%1d\nBLOCK_SIZE\t%1d\nLUT_MEMORY\t%1d\nOUTPUT_REG\t%1d\nGLOB_STATE\t%1d\n",
            DATA_WIDTH,FLOWS,BLOCK_SIZE,LUT_MEMORY,OUTPUT_REG,GLOB_STATE);  
            
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


