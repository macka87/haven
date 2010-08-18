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
 * $Id: test.sv 6067 2008-10-24 14:51:49Z xsanta06 $
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
  iNFifoRx.nfifo_write_tb FW[FLOWS],
  iNFifoRx.mem_read_tb    MR,
  iNFifoRx.mem_monitor    MONITOR
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  // AK MA KOMPONENTA VIAC DRIVEROV ALEBO MONITOROV TREBA ICH NA TOMTO MIESTE DEKLAROVAT A V TASKU
  // CREATEENVIRONMENT INSTANCIOVAT
  
  // Transaction
  BufferTransaction                                                   buffBlueprint;                  
  // Generator 
  Generator                                                           generator[FLOWS]; 
  // Driver 
  nFifoDriver #(DRIVER0_DATA_WIDTH,DRIVER0_FLOWS,DRIVER0_BLOCK_SIZE,
                 DRIVER0_LUT_MEMORY, DRIVER0_GLOB_STATE)              fDriver[FLOWS];
  // Monitor
  MemMonitor #(MONITOR0_DATA_WIDTH,MONITOR0_FLOWS,MONITOR0_BLOCK_SIZE,
                 MONITOR0_LUT_MEMORY, MONITOR0_GLOB_STATE, MONITOR0_OUTPUT_REG)
                                                                      fMonitor;   
  // Responder
  MemResponder #(MONITOR0_DATA_WIDTH,MONITOR0_FLOWS,MONITOR0_BLOCK_SIZE,
                 MONITOR0_LUT_MEMORY, MONITOR0_GLOB_STATE)            fResponder;   
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
    for(int i=0; i<FLOWS; i++) begin
      generator[i] = new("Generator", i);
      buffBlueprint = new;
      buffBlueprint.dataSize   = GENERATOR0_DATA_SIZE;
      buffBlueprint.flowCount  = GENERATOR0_FLOW_COUNT;
      generator[i].blueprint = buffBlueprint;
    end;   
   
    // Create scoreboard
    scoreboard = new;
    
    // Coverage class
    coverage = new();
      
    // Create and connect driver 
    if (FLOWS>0) 
    begin  
      fDriver[0] = new ("Driver0", 0, generator[0].transMbx, FW[0]);
      coverage.addGeneralInterfaceWrite(FW[0],"FWcoverage0");
    end 
     
    if (FLOWS>1)
    begin
      fDriver[1] = new ("Driver1", 1, generator[1].transMbx, FW[1]);
      coverage.addGeneralInterfaceWrite(FW[1],"FWcoverage1");
    end  
    
    if (FLOWS>2) 
    begin
      fDriver[2] = new ("Driver2", 2, generator[2].transMbx, FW[2]);
      coverage.addGeneralInterfaceWrite(FW[2],"FWcoverage2");
      fDriver[3] = new ("Driver3", 3, generator[3].transMbx, FW[3]);
      coverage.addGeneralInterfaceWrite(FW[3],"FWcoverage3");
    end
    
    if (FLOWS>4) 
    begin
      fDriver[4] = new ("Driver4", 4, generator[4].transMbx, FW[4]);
      coverage.addGeneralInterfaceWrite(FW[4],"FWcoverage4");
      fDriver[5] = new ("Driver5", 5, generator[5].transMbx, FW[5]);
      coverage.addGeneralInterfaceWrite(FW[5],"FWcoverage5");
      fDriver[6] = new ("Driver6", 6, generator[6].transMbx, FW[6]);
      coverage.addGeneralInterfaceWrite(FW[6],"FWcoverage6");
      fDriver[7] = new ("Driver7", 7, generator[7].transMbx, FW[7]);
      coverage.addGeneralInterfaceWrite(FW[7],"FWcoverage7");
    end  

    for(int i=0; i<FLOWS; i++) begin
       fDriver[i].fwDelayEn_wt             = DRIVER0_DELAYEN_WT; 
       fDriver[i].fwDelayDisable_wt        = DRIVER0_DELAYDIS_WT;
       fDriver[i].fwDelayLow               = DRIVER0_DELAYLOW;
       fDriver[i].fwDelayHigh              = DRIVER0_DELAYHIGH;
       fDriver[i].setCallbacks(scoreboard.driverCbs);
    end;
    
    // Create and connect responder
    fResponder = new ("Responder", MR);
      fResponder.frDelayEn_wt               = MONITOR0_DELAYEN_WT; 
      fResponder.frDelayDisable_wt          = MONITOR0_DELAYDIS_WT;   
      fResponder.frDelayLow                 = MONITOR0_DELAYLOW;
      fResponder.frDelayHigh                = MONITOR0_DELAYHIGH;
      fResponder.pipeDelayEn_wt             = MONITOR0_PIPEEN_WT; 
      fResponder.pipeDelayDisable_wt        = MONITOR0_PIPEDIS_WT;   
      fResponder.pipeDelayLow               = MONITOR0_PIPELOW;
      fResponder.pipeDelayHigh              = MONITOR0_PIPEHIGH;  

    // Create and connect monitor
    fMonitor = new ("Monitor", MONITOR, fResponder.dontRead);
    coverage.addGeneralInterfaceMonitor(MONITOR,"FRcoverage");
    fMonitor.setCallbacks(scoreboard.monitorCbs);

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
    // V PRIPADE POTREBY ZAPNUT VSETKY POUZITE DRIVERY A MONITORY 
    for(int i=0; i<FLOWS; i++) 
        fDriver[i].setEnabled();
    fMonitor.setEnabled();
    fResponder.setEnabled();
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Enviroment
  task disableTestEnvironment();
     // V PRIPADE POTREBY VYPNUT VSETKY POUZITE DRIVERY A MONITORY
     // Disable drivers
    #(1000*CLK_PERIOD);
    for(int i=0; i<FLOWS; i++) 
        fDriver[i].setDisabled();
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
     for(int i=0; i<FLOWS; i++) begin 
        generator[i].setEnabled(TRANSACTION_COUNT);
     end
     
     // Pokud je generator aktivni nic nedelej 
    for(int i=0; i<FLOWS; i++) begin   
    while (generator[i].enabled)
      #(CLK_PERIOD);
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


