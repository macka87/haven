/*
 * test.sv: TX DMA Controller automatic test
 * Copyright (C) 2008 CESNET
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
 * $Id: test.sv 12979 2010-02-26 16:13:08Z kastovsky $
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import sv_tx_dma_ctrl_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic         CLK,
  output logic         RESET,
  iMi32.tb        SW,
  iInternalBus.ib_write_tb IB,
  iDmaCtrl.misc_tb     MISC[BUFFER_FLOWS],
  iDmaCtrl.desc_tb     DESC[BUFFER_FLOWS],
  iDmaCtrl.dma_tb      DMA[BUFFER_FLOWS],
  iFrameLinkTx.tb      FL[BUFFER_FLOWS],
  iFrameLinkTx.monitor MONITOR[BUFFER_FLOWS]
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  
  // Transaction
  FrameLinkTransaction   flBlueprint; 
  // Generator                            
  Generator              generator;
  // Driver                               
  TxDmaCtrlDriver #(DRIVER0_DATA_WIDTH, CTRL_DMA_DATA_WIDTH, BUFFER_FLOWS, 
                    DRIVER0_PAGE_SIZE, DRIVER0_PAGE_COUNT)       driver; 
  // SW driver
  TxIbusModul #(DRIVER0_DATA_WIDTH, CTRL_DMA_DATA_WIDTH, BUFFER_FLOWS,
               DRIVER0_PAGE_SIZE, DRIVER0_PAGE_COUNT)            ibDriver;  
  // Monitor      
  FrameLinkMonitor #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH, BUFFER_FLOWS)   flMonitor[BUFFER_FLOWS]; 
  // Responder     
  FrameLinkResponder #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) flResponder[BUFFER_FLOWS];
  // Scoreboard  
  Scoreboard #(BUFFER_FLOWS)            scoreboard; 
  // Coverage                             
  Coverage #(DRIVER0_DATA_WIDTH, CTRL_DMA_DATA_WIDTH, MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) coverage; 
  
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
      flBlueprint.flowCount     = BUFFER_FLOWS;
      flBlueprint.packetSizeMax = GENERATOR_PACKET_SIZE_MAX;
      flBlueprint.packetSizeMin = GENERATOR_PACKET_SIZE_MIN;
      assert(flBlueprint.randomize());
      generator.blueprint = flBlueprint;
    
    // Create scoreboard
    scoreboard = new;
    
    // Create driver    
    driver    = new ("Driver0", generator.transMbx, SW, DESC);
      driver.setCallbacks(scoreboard.driverCbs);
    ibDriver  = new ("IbDriver0",driver, IB, DMA);
    
    // Create monitor  
    flMonitor[0] = new ("Monitor0", 0, MONITOR[0]);
    flMonitor[1] = new ("Monitor1", 1, MONITOR[1]);
    flMonitor[2] = new ("Monitor1", 2, MONITOR[2]);
    flMonitor[3] = new ("Monitor1", 3, MONITOR[3]);
      for (int i=0; i<BUFFER_FLOWS; i++)
        flMonitor[i].setCallbacks(scoreboard.monitorCbs);
    
    // Create responder
    flResponder[0] = new ("Responder0", FL[0]);
    flResponder[1] = new ("Responder1", FL[1]);
    flResponder[2] = new ("Responder1", FL[2]);
    flResponder[3] = new ("Responder1", FL[3]);    
      for (int i=0; i<BUFFER_FLOWS; i++)
      begin
        flResponder[i].rxDelayEn_wt            = MONITOR0_DELAYEN_WT; 
        flResponder[i].rxDelayDisable_wt       = MONITOR0_DELAYDIS_WT;
        flResponder[i].rxDelayLow              = MONITOR0_DELAYLOW;
        flResponder[i].rxDelayHigh             = MONITOR0_DELAYHIGH;
        flResponder[i].insideRxDelayEn_wt      = MONITOR0_INSIDE_DELAYEN_WT; 
        flResponder[i].insideRxDelayDisable_wt = MONITOR0_INSIDE_DELAYDIS_WT;
        flResponder[i].insideRxDelayLow        = MONITOR0_INSIDE_DELAYLOW;
        flResponder[i].insideRxDelayHigh       = MONITOR0_INSIDE_DELAYHIGH;    
      end    
    
    // Coverage class
    coverage = new();
      coverage.addDmaInterface (DMA[0],"DMAcoverage0");
      coverage.addDmaInterface (DMA[1],"DMAcoverage1");
      coverage.addDmaInterface (DMA[2],"DMAcoverage2");
      coverage.addDmaInterface (DMA[3],"DMAcoverage3");  
      coverage.addDescriptorInterface (DESC[0],"DESCcoverage0");
      coverage.addDescriptorInterface (DESC[1],"DESCcoverage1");
      coverage.addDescriptorInterface (DESC[2],"DESCcoverage2");
      coverage.addDescriptorInterface (DESC[3],"DESCcoverage3"); 
      coverage.addInternalBusInterface (IB,"IBcoverage");
      coverage.addMI32Interface (SW,"SWcoverage");
      coverage.addFrameLinkInterface (FL[0],"FLcoverage0");
      coverage.addFrameLinkInterface (FL[1],"FLcoverage1");
      coverage.addFrameLinkInterface (FL[2],"FLcoverage2");
      coverage.addFrameLinkInterface (FL[3],"FLcoverage3");
        
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
    driver.setEnabled();
    ibDriver.setEnabled();
    
    for(int i=0; i<BUFFER_FLOWS; i++)
    begin
      flMonitor[i].setEnabled();
      flResponder[i].setEnabled();
    end
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
     // Disable drivers
     #(5000*CLK_PERIOD); 
     driver.setDisabled();
     #(10000*CLK_PERIOD);
     ibDriver.setDisabled();
     // Disable monitors     
     for (int i=0;i<BUFFER_FLOWS; i++)
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
    $write("BUFFER_DATA_WIDTH:\t%1d\nBUFFER_FLOWS:\t%1d\nBUFFER_BLOCK_SIZE:\t%1d\nBUFFER_TOTAL_FLOW_SIZE:\t%1d\nCTRL_BUFFER_ADDR:\t%1d\nCTRL_DMA_DATA_WIDTH:\t%1d\n",BUFFER_DATA_WIDTH,BUFFER_FLOWS,BUFFER_BLOCK_SIZE,BUFFER_TOTAL_FLOW_SIZE,CTRL_BUFFER_ADDR,CTRL_DMA_DATA_WIDTH);
    $write("\n------------ RAM PARAMETERS -------------------\n\n");
    $write("PAGE_SIZE:\t%1d\nPAGE_COUNT:\t%1d\n",DRIVER0_PAGE_SIZE,DRIVER0_PAGE_COUNT);
    $write("\n------------ TRANSACTION PARAMETERS------------\n\n");
    $write("TRANSACTION_COUNT:\t%1d\n",TRANSACTION_COUNT);
    
    test1();       // Run Test 1
    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $stop();       // Stop testing
  end

endprogram

