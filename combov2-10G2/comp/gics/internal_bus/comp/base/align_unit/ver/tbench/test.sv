/*
 * test.sv: IB_SWITCH automatic test
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
 * $Id: test.sv 3590 2008-07-16 09:05:59Z xsanta06 $
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import sv_au_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
// V PRIPADE POTREBY DOPLNIT FRAMELINKOVE ROZHRANIA
program TEST (
  input  logic     CLK,
  output logic     RESET,
  iAlignUnit.rx_tb   RX,
  iAlignUnit.tx_tb   TX,
  iAlignUnit.monitor MONITOR
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
 
  // AK MA KOMPONENTA VIAC DRIVEROV ALEBO MONITOROV TREBA ICH NA TOMTO 
  // MIESTE DEKLAROVAT A V TASKU CREATEENVIRONMENT INSTANCIOVAT
  
  // Transaction
  AlignUnitTransaction    auBlueprint; 
  // Generator                            
  Generator               generator;
  // Driver                               
  AlignUnitDriver         auDriver; 
  // Monitor      
  AlignUnitMonitor        auMonitor; 
  // Responder     
  AlignUnitResponder      auResponder;
  // Scoreboard  
  Scoreboard              scoreboard; 
  // Coverage                             
  Coverage                coverage;
  
  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createEnvironment();  
    // Create generator
    generator = new("Generator0", 0);
    auBlueprint = new;
    auBlueprint.dataSizeMin   = DATA_SIZE_MIN;
    auBlueprint.dataSizeMax   = DATA_SIZE_MAX;
    generator.blueprint       = auBlueprint;
        
    // Create scoreboard
    scoreboard = new();
    
    // Create driver    
    auDriver  = new ("Driver0", generator.transMbx, RX, scoreboard.tr_info);
      auDriver.rxDelayEn_wt             = DRIVER0_DELAYEN_WT; 
      auDriver.rxDelayDisable_wt        = DRIVER0_DELAYDIS_WT;
      auDriver.rxDelayLow               = DRIVER0_DELAYLOW;
      auDriver.rxDelayHigh              = DRIVER0_DELAYHIGH;
      auDriver.insideRxDelayEn_wt       = DRIVER0_INSIDE_DELAYEN_WT; 
      auDriver.insideRxDelayDisable_wt  = DRIVER0_INSIDE_DELAYDIS_WT;
      auDriver.insideRxDelayLow         = DRIVER0_INSIDE_DELAYLOW;
      auDriver.insideRxDelayHigh        = DRIVER0_INSIDE_DELAYHIGH;
    // Create monitor
    auMonitor = new ("Monitor0", MONITOR, scoreboard.tr_info);
    // Create responder
    auResponder = new ("Responder0", TX);
      auResponder.txDelayEn_wt            = MONITOR0_DELAYEN_WT; 
      auResponder.txDelayDisable_wt       = MONITOR0_DELAYDIS_WT;
      auResponder.txDelayLow              = MONITOR0_DELAYLOW;
      auResponder.txDelayHigh             = MONITOR0_DELAYHIGH;
      auResponder.insideTxDelayEn_wt      = MONITOR0_INSIDE_DELAYEN_WT; 
      auResponder.insideTxDelayDisable_wt = MONITOR0_INSIDE_DELAYDIS_WT;
      auResponder.insideTxDelayLow        = MONITOR0_INSIDE_DELAYLOW;
      auResponder.insideTxDelayHigh       = MONITOR0_INSIDE_DELAYHIGH;    
    
    // Coverage class
    // V PRIPADE VIAC INTERFACOV TREBA VOLAT PRISLUSNY 
    // COVERAGE PODLA TYPU INTERFACE
    coverage = new();
      coverage.addAlignUnitInterfaceRx(RX,"RXcoverage");
      coverage.addAlignUnitInterfaceTx(MONITOR,"TXcoverage");
    // Set Callbacks
    // V PRIPADE VIAC DRIVEROV ALEBO MONITOROV TREBA VOLAT PRISLUSNE CALLBACKS
      auDriver.setCallbacks(scoreboard.driverCbs);
      auMonitor.setCallbacks(scoreboard.monitorCbs);
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
  // Enable test Environment
  task enableTestEnvironment();
    // Enable Driver, Monitor, Coverage for each port
    // V PRIPADE POTREBY ZAPNUT VSETKY POUZITE DRIVERY A MONITORY A RESPONDERY
    auDriver.setEnabled();
    auMonitor.setEnabled();
//    auResponder.setEnabled();
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
     // V PRIPADE POTREBY VYPNUT VSETKY POUZITE DRIVERY A MONITORY A RESPONDERY
     // Disable drivers
     #(1000*CLK_PERIOD); 
     auDriver.setDisabled();
     // Disable monitors
     auMonitor.setDisabled();
     auResponder.setDisabled();
     coverage.setDisabled();
  endtask : disableTestEnvironment

  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Test Case 1
  task test1();
     $write("\n\n############ TEST CASE 1 ############\n\n");
     // Enable Test environment
     enableTestEnvironment();
     // Run generators
     generator.setEnabled(TRANSACTION_COUT);

     // Pokud je generator aktivni nic nedelej
     while (generator.enabled) begin
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

