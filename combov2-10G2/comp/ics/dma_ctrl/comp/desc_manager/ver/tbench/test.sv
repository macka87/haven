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
 * $Id: test.sv 5193 2008-08-25 07:46:02Z xsimko03 $
 *
 * TODO:
 *
 */

import test_pkg::*;
import sv_common_pkg::*;
import dm_transaction_pkg::*;
import driver_pkg::*;       
import monitor_pkg::*;      
import responder_pkg::*;      
import scoreboard_pkg::*;  
import coverage_pkg::*;     

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic           CLK,
  output logic           RESET,  
  
  descManagerWrite.writeDesc_tb DW,            // Write Interface
  descManagerRead.readDesc_tb   DR[FLOWS],     // Read Interface
  descManagerRead.monitor       MONITOR[FLOWS] // Monitor Interface
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  // AK MA KOMPONENTA VIAC DRIVEROV ALEBO MONITOROV TREBA ICH NA TOMTO MIESTE DEKLAROVAT A V TASKU
  // CREATEENVIRONMENT INSTANCIOVAT
  
  // Transaction
  descManagerTransaction                                                                 dmBlueprint;                  
  // Generator 
  Generator                                                                              generator; 
  // Driver 
  descManagerDriver #(DRIVER0_BASE_ADDR, DRIVER0_FLOWS, DRIVER0_BLOCK_SIZE, DRIVER0_RANGE, INIT_OFFSET) dDriver;
  // Monitor
  descManagerMonitor #(MONITOR0_BASE_ADDR, MONITOR0_FLOWS, MONITOR0_BLOCK_SIZE)          dMonitor[FLOWS];   
  // Responder
  descManagerResponder #(MONITOR0_BASE_ADDR,  MONITOR0_FLOWS, MONITOR0_BLOCK_SIZE)       dResponder[FLOWS];   
  // Scoreboard
  Scoreboard                                                                             scoreboard;
  // Coverage
  Coverage #(BASE_ADDR, FLOWS, BLOCK_SIZE)                                               coverage;  
  
  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------  
  // Create Test Environment
  task createEnvironment();
    // Create generator
    generator = new("Generator0", 0);
    dmBlueprint = new;
    dmBlueprint.dataSize   = GENERATOR0_DATA_SIZE;
    generator.blueprint    = dmBlueprint;
    
    // Create scoreboard
    scoreboard = new;

    // Create driver    
    dDriver = new ("Driver0", generator.transMbx, DW);
    dDriver.fwDelayEn_wt             = DRIVER0_DELAYEN_WT; 
    dDriver.fwDelayDisable_wt        = DRIVER0_DELAYDIS_WT;
    dDriver.fwDelayLow               = DRIVER0_DELAYLOW;
    dDriver.fwDelayHigh              = DRIVER0_DELAYHIGH;
    dDriver.setCallbacks(scoreboard.driverCbs);
    
    // Create monitor
    // MUST BE CONSTANTS :(
    
    dMonitor[0]  = new ("Monitor0" ,0,  MONITOR[0]);
    dMonitor[1]  = new ("Monitor1" ,1,  MONITOR[1]);
    dMonitor[2]  = new ("Monitor2" ,2,  MONITOR[2]);
    dMonitor[3]  = new ("Monitor3" ,3,  MONITOR[3]);
    dMonitor[4]  = new ("Monitor4" ,4,  MONITOR[4]);
    dMonitor[5]  = new ("Monitor5" ,5,  MONITOR[5]);
    dMonitor[6]  = new ("Monitor6" ,6,  MONITOR[6]);
    dMonitor[7]  = new ("Monitor7" ,7,  MONITOR[7]);
    /*dMonitor[8]  = new ("Monitor8" ,8,  MONITOR[8]);
    dMonitor[9]  = new ("Monitor9" ,9,  MONITOR[9]);
    dMonitor[10] = new ("Monitor10",10, MONITOR[10]);
    dMonitor[11] = new ("Monitor10",11, MONITOR[11]);
    dMonitor[12] = new ("Monitor10",12, MONITOR[12]);
    dMonitor[13] = new ("Monitor10",13, MONITOR[13]);
    dMonitor[14] = new ("Monitor10",14, MONITOR[14]);
    dMonitor[15] = new ("Monitor10",15, MONITOR[15]);*/
    
    // Create responder
    // MUST BE CONSTANTS :(
      dResponder[0]  = new ("Responder0",  DR[0]);
      dResponder[1]  = new ("Responder1",  DR[1]);
      dResponder[2]  = new ("Responder2",  DR[2]);
      dResponder[3]  = new ("Responder3",  DR[3]);
      dResponder[4]  = new ("Responder4",  DR[4]);
      dResponder[5]  = new ("Responder5",  DR[5]);
      dResponder[6]  = new ("Responder6",  DR[6]);
      dResponder[7]  = new ("Responder7",  DR[7]);
      /*dResponder[8]  = new ("Responder8",  DR[8]);
      dResponder[9]  = new ("Responder9",  DR[9]);
      dResponder[10] = new ("Responder10", DR[10]);
      dResponder[11] = new ("Responder11", DR[11]);
      dResponder[12] = new ("Responder12", DR[12]);
      dResponder[13] = new ("Responder13", DR[13]);
      dResponder[14] = new ("Responder14", DR[14]);
      dResponder[15] = new ("Responder15", DR[15]);*/
    
    // Connect monitors and responders
    for(int i=0; i<FLOWS; i++) begin
      dResponder[i].frDelayEn_wt               = MONITOR0_DELAYEN_WT; 
      dResponder[i].frDelayDisable_wt          = MONITOR0_DELAYDIS_WT;   
      dResponder[i].frDelayLow                 = MONITOR0_DELAYLOW;
      dResponder[i].frDelayHigh                = MONITOR0_DELAYHIGH;
      dMonitor[i].setCallbacks(scoreboard.monitorCbs);
    end;
    
    // Coverage class
    coverage = new();
    coverage.addGeneralInterfaceWrite(DW,"BWcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[0], "DRcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[1], "DRcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[2], "DRcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[3], "DRcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[4], "BRcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[5], "BRcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[6], "BRcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[7], "BRcoverage");
    /*coverage.addGeneralInterfaceMonitor(MONITOR[8], "DRcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[9], "DRcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[10],"DRcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[11],"DRcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[12],"BRcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[13],"BRcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[14],"BRcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[15],"BRcoverage");*/
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
    dDriver.setEnabled();
    for(int i=0; i<FLOWS; i++) begin
      dMonitor[i].setEnabled();
      dResponder[i].setEnabled();
      end
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Enviroment
  task disableTestEnvironment();
     // V PRIPADE POTREBY VYPNUT VSETKY POUZITE DRIVERY A MONITORY
     // Disable drivers
    #(1000*CLK_PERIOD);
    dDriver.setDisabled();
    #(12000*CLK_PERIOD);
    for(int i=0; i<FLOWS; i++) begin
      dMonitor[i].setDisabled();
      dResponder[i].setDisabled();
      end
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
