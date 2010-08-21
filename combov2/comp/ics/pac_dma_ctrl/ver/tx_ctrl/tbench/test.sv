/*
 * test.sv: TX PAC DMA Controller automatic test
 * Copyright (C) 2009 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
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
 * $Id: test.sv 9399 2009-07-14 19:51:39Z xsanta06 $
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import sv_fl_pkg::*;
import sv_tx_pac_ctrl_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic             CLK,
  output logic             RESET,
  iInternalBus.ib_write_tb IB,
  iPacDmaCtrl.misc_tb      MISC,
  iPacDmaCtrl.desc_tb      DESC,
  iPacDmaCtrl.stattx_tb    SU,
  iDmaCtrl.dma_tb          DMA,
  iFrameLinkTx.tb          FL[FLOWS],
  iFrameLinkTx.monitor     MONITOR[FLOWS]
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  
  // Transaction
  FrameLinkTransaction      flBlueprint; 
  // Generator                            
  Generator                 generator;
  // Misc Driver
  TxMiscDriver    #(FLOWS)  miscDriver;
  // Driver                               
  TxDmaCtrlDriver #(FLOWS, NUM_FLAGS, RAM_SIZE, MAX_DESC_LENGTH) driver; 
  // IB driver
  TxIbusModul     #(DRIVER0_DATA_WIDTH, CTRL_DMA_DATA_WIDTH, FLOWS, 
                    NUM_FLAGS, CTRL_DMA_ID, TRANS_TYPE, RAM_SIZE, 
                    MAX_DESC_LENGTH)                             ibDriver;  
  // DMA modul
  DmaModul        #(CTRL_DMA_DATA_WIDTH, CTRL_DMA_ID, TRANS_TYPE)dmaModul;
  // Descriptor Manager
  TxDescManager   #(FLOWS)                                       descManager;
  // Status Update Manager
  TxSuManager     #(FLOWS, NUM_FLAGS, RAM_SIZE, MAX_DESC_LENGTH) suManager;
  // Monitor      
  FrameLinkMonitor #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH)   flMonitor[FLOWS]; 
  // Responder     
  FrameLinkResponder #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) flResponder[FLOWS];
  // Scoreboard  
  Scoreboard      #(FLOWS, 1)                         scoreboard; 
  // Coverage                             
  TxPacCoverage   #(DRIVER0_DATA_WIDTH, FLOWS, CTRL_DMA_DATA_WIDTH, 
                    MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH)    coverage; 
 
  // Only array of virtual interfaces can be indexed
  virtual iFrameLinkTx.tb      #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) vTX[FLOWS];
  virtual iFrameLinkTx.monitor #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) vMONITOR[FLOWS];
  
  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createEnvironment();  
    // Create generator    
    generator= new("Generator", 0);
      flBlueprint = new;
      flBlueprint.packetCount   = GENERATOR_PACKET_COUNT;
      flBlueprint.packetSizeMax = GENERATOR_PACKET_SIZE_MAX;
      flBlueprint.packetSizeMin = GENERATOR_PACKET_SIZE_MIN;
      generator.blueprint = flBlueprint;
    
    // Assign virtual interfaces
    vTX = FL;
    vMONITOR = MONITOR;
    
    // Create scoreboard
    scoreboard = new;
    
    // Coverage class
    coverage = new();

    // Create driver    
    miscDriver  = new("MISC Driver", MISC);
      miscDriver.delayEn_wt      = RUN_DELAYEN_WT; 
      miscDriver.delayDisable_wt = RUN_DELAYDIS_WT;
      miscDriver.delayLow        = RUN_INSIDE_DELAYLOW;
      miscDriver.delayHigh       = RUN_INSIDE_DELAYHIGH;
    dmaModul    = new ("DMA modul", DMA);
      coverage.addDmaInterface (DMA,"DMA Coverage");
    descManager = new ("Descriptor Manager", DESC);
      descManager.delayEn_wt      = DESC_MANAGER_DELAYEN_WT; 
      descManager.delayDisable_wt = DESC_MANAGER_DELAYDIS_WT;
      descManager.delayLow        = DESC_MANAGER_INSIDE_DELAYLOW;
      descManager.delayHigh       = DESC_MANAGER_INSIDE_DELAYHIGH;
      coverage.addDescriptorInterface (DESC,"DESC Coverage");
    driver    = new ("Driver", generator.transMbx, descManager);
      driver.setCallbacks(scoreboard.driverCbs);
    ibDriver  = new ("IB Driver", driver, dmaModul, IB);
      coverage.addInternalBusInterface (IB,"IB Coverage");
    suManager = new ("Status Update Manager", driver, SU);
      coverage.addStatusUpdateInterface (SU,"SU Coverage");
    
    // Create monitor and responder
    for (int i=0; i<FLOWS; i++)
    begin
      string monitorLabel;
      string responderLabel;
      string coverageLabel;

      $swrite(monitorLabel, "Monitor %0d", i);
      $swrite(responderLabel, "Responder %0d", i);
      $swrite(coverageLabel, "FL Coverage %0d", i);
      flMonitor[i]   = new (monitorLabel, vMONITOR[i]);
      flResponder[i] = new (responderLabel, vTX[i]);

      flResponder[i].rxDelayEn_wt            = MONITOR0_DELAYEN_WT; 
      flResponder[i].rxDelayDisable_wt       = MONITOR0_DELAYDIS_WT;
      flResponder[i].rxDelayLow              = MONITOR0_DELAYLOW;
      flResponder[i].rxDelayHigh             = MONITOR0_DELAYHIGH;
      flResponder[i].insideRxDelayEn_wt      = MONITOR0_INSIDE_DELAYEN_WT; 
      flResponder[i].insideRxDelayDisable_wt = MONITOR0_INSIDE_DELAYDIS_WT;
      flResponder[i].insideRxDelayLow        = MONITOR0_INSIDE_DELAYLOW;
      flResponder[i].insideRxDelayHigh       = MONITOR0_INSIDE_DELAYHIGH;    
      flMonitor[i].setCallbacks(scoreboard.monitorCbs);
      coverage.addFrameLinkInterface (vTX[i],coverageLabel);
    end    
    
        
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
    miscDriver.setEnabled();
    driver.setEnabled();
    ibDriver.setEnabled();
    descManager.setEnabled();
    suManager.setEnabled();
    dmaModul.setEnabled();
    
    for(int i=0; i<FLOWS; i++)
    begin
      flMonitor[i].setEnabled();
      flResponder[i].setEnabled();
    end
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
     bit busy;
     int i = 0;

     // Disable drivers
     #(5000*CLK_PERIOD); 
     miscDriver.setDisabled();
     driver.setDisabled();

     // Check if monitors are not receiving transaction for 100 CLK_PERIODs
     while (i<100) begin
       busy = 0;
       for (int j=0; j<FLOWS; j++)
         if (flMonitor[j].busy == 1) busy = 1;
       if (busy) i = 0;
       else i++;
       #(CLK_PERIOD); 
     end

     ibDriver.setDisabled();
     descManager.setDisabled();
     suManager.setDisabled();
     dmaModul.setDisabled();

     // Disable monitors     
     for (int i=0;i<FLOWS; i++)
     begin
       flMonitor[i].setDisabled();
       flResponder[i].setDisabled();
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
     // Enable Test environment
     enableTestEnvironment();
     // Run generators
     generator.setEnabled(TRANSACTION_COUNT);

     // While generator is active do nothing
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
    #(10*CLK_PERIOD);
    createEnvironment(); // Create Test Enviroment
    // -------------------------------------
    // TESTING
    // -------------------------------------
    $write("\n\n############ GENERICS AND PARAMETERS ############\n\n");
    $write("------------ DUT GENERICS ---------------------\n\n");
    $write("FLOWS:\t\t\t%0d\nBUFFER_DATA_WIDTH:\t\t%0d\nBUFFER_BLOCK_SIZE:\t\t%0d\nBUFFER_TOTAL_FLOW_SIZE:\t%0d\nCTRL_BUFFER_ADDR:\t\t%0d\nCTRL_BUFFER_GAP:\t\t%0hh\nCTRL_BUFFER_SIZE:\t\t%0d\nCTRL_DMA_ID:\t\t\t%0d\nCTRL_DMA_DATA_WIDTH:\t\t%0d\nCTRL_BLOCK_SIZE:\t\t%0d\n",FLOWS,BUFFER_DATA_WIDTH,BUFFER_BLOCK_SIZE,BUFFER_TOTAL_FLOW_SIZE,CTRL_BUFFER_ADDR,CTRL_BUFFER_GAP,CTRL_BUFFER_SIZE,CTRL_DMA_ID,CTRL_DMA_DATA_WIDTH,CTRL_BLOCK_SIZE);
    
    test1();       // Run Test 1
   // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $stop();       // Stop testing
  end

endprogram

