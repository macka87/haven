/*
 * test.sv: Status Update Manager automatic test
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
 * $Id: test.sv 11736 2009-10-25 11:01:35Z xsanta06 $
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import sv_fl_pkg::*;
import sv_mi32_pkg::*;
import sv_sum_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic             CLK,
  output logic             RESET,
  iSum.misc_tb             MISC,
  iInternalBus.ib_read_tb  IB,
  iDmaCtrl.dma_tb          DMA,
  iMi32.tb                 MI32,
  iSum.reqFifo_tb          REQ,
  iSu.su_tb                RX_SU,
  iSu.su_tb                TX_SU
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  
  // Transaction
  SumMi32Transaction        miBlueprint; 
  StatusUpdateTransaction   txSuBlueprint; 
  StatusUpdateTransaction   rxSuBlueprint; 
  SumRfTransaction          rfBlueprint; 
  // Generator                            
  Generator                 miGenerator;
  Generator                 txSuGenerator;
  Generator                 rxSuGenerator;
  Generator                 rfGenerator;
  // MI32 Driver
  Mi32Driver                miDriver;
  // Misc Driver
  SumMiscDriver   #(FLOWS, BLOCK_SIZE)                         miscDriver;
  // Driver                               
  SuDriver        #(FLOWS, TX_SU_DATA_SIZE)                    txSuDriver; 
  SuDriver        #(FLOWS, RX_SU_DATA_SIZE)                    rxSuDriver; 
  SumRfDriver     #(FLOWS, BLOCK_SIZE)                         rfDriver; 
  // IB monitor
  SumIbMonitor    #(MONITOR0_DATA_WIDTH, DMA_DATA_WIDTH, FLOWS, 
                    TX_GADDR, DMA_ID, TRANS_TYPE)              ibMonitor;  
  // DMA modul
  DmaModul        #(DMA_DATA_WIDTH, DMA_ID, TRANS_TYPE)        dmaModul;
  // Timeout module
  SumTimeoutModule #(FLOWS)                                    timeoutModule;
  // Scoreboard  
  Scoreboard      #(FLOWS, 0)                                  scoreboard; 
  // Checker  
  SumChecker      #(FLOWS)                                     checker; 
  // Reference Model  
  SumReferenceModel #(FLOWS, BLOCK_SIZE, MONITOR0_DATA_WIDTH, 
                      RX_SU_DATA_SIZE, TX_SU_DATA_SIZE, 
                      DMA_DATA_WIDTH)                          refModel; 
//  // Coverage                             
//  TxPacCoverage   #(DRIVER0_DATA_WIDTH, FLOWS, CTRL_DMA_DATA_WIDTH, 
//                    MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH)    coverage; 
  
  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createEnvironment();  
    // Create generator    
    miGenerator= new("MI32 Generator", 0);
      miBlueprint = new;
      miBlueprint.txGAddr = TX_GADDR;
      miGenerator.blueprint = miBlueprint;
    
    txSuGenerator= new("TX SU Generator", 0);
      txSuBlueprint = new;
      txSuBlueprint.maxAddress  = FLOWS;
      txSuBlueprint.dataSize    = TX_SU_DATA_SIZE;
      txSuBlueprint.rxType      = 0;    
      txSuBlueprint.intFlag0_wt = TX_UPDATE_INTF0_WT;
      txSuBlueprint.intFlag1_wt = TX_UPDATE_INTF1_WT;
      txSuBlueprint.lfFlag0_wt  = TX_UPDATE_LFF0_WT;
      txSuBlueprint.lfFlag1_wt  = TX_UPDATE_LFF1_WT;
      txSuGenerator.blueprint = txSuBlueprint;
    
    rxSuGenerator= new("RX SU Generator", 0);
      rxSuBlueprint = new;
      rxSuBlueprint.maxAddress  = FLOWS;
      rxSuBlueprint.dataSize    = RX_SU_DATA_SIZE;
      rxSuBlueprint.rxType      = 1;    
      rxSuBlueprint.intFlag0_wt = RX_UPDATE_INTF0_WT;
      rxSuBlueprint.intFlag1_wt = RX_UPDATE_INTF1_WT;
      rxSuBlueprint.lfFlag0_wt  = RX_UPDATE_LFF0_WT;
      rxSuBlueprint.lfFlag1_wt  = RX_UPDATE_LFF1_WT;
      rxSuGenerator.blueprint = rxSuBlueprint;
    
    rfGenerator= new("RF Generator", 0);
      rfBlueprint = new;
      rfBlueprint.blockSize   = BLOCK_SIZE;
      rfGenerator.blueprint = rfBlueprint;
    
    timeoutModule = new ("Timeout Module", miGenerator.transMbx);
      timeoutModule.timeoutLow         = TIMEOUT_LOW;
      timeoutModule.timeoutHigh        = TIMEOUT_HIGH;
      
    miDriver = new ("MI32 Driver", miGenerator.transMbx, MI32);
      miDriver.txDelayEn_wt            = 0; 
      miDriver.txDelayDisable_wt       = 1;

    // Create scoreboard
    scoreboard = new;
    // Create checker
    checker = new("CHECKER");
    
//    // Coverage class
//    coverage = new();

    // Create driver    
    miscDriver  = new("MISC Driver", MISC);

    dmaModul    = new ("DMA modul", DMA);
//      coverage.addDmaInterface (DMA,"DMA Coverage");

    txSuDriver  = new ("TX SU Driver", txSuGenerator.transMbx, TX_SU);
      txSuDriver.delayEn_wt          = TX_SU_DRIVER_DELAYEN_WT;
      txSuDriver.delayDisable_wt     = TX_SU_DRIVER_DELAYDIS_WT;
      txSuDriver.delayLow            = TX_SU_DRIVER_DELAYLOW;
      txSuDriver.delayHigh           = TX_SU_DRIVER_DELAYHIGH;
      txSuDriver.setCallbacks(checker.driverCbs);

    rxSuDriver  = new ("RX SU Driver", rxSuGenerator.transMbx, RX_SU);
      rxSuDriver.delayEn_wt          = RX_SU_DRIVER_DELAYEN_WT;
      rxSuDriver.delayDisable_wt     = RX_SU_DRIVER_DELAYDIS_WT;
      rxSuDriver.delayLow            = RX_SU_DRIVER_DELAYLOW;
      rxSuDriver.delayHigh           = RX_SU_DRIVER_DELAYHIGH;
      rxSuDriver.setCallbacks(scoreboard.driverCbs);

    rfDriver    = new ("RF Driver", rfGenerator.transMbx, REQ);
      rfDriver.delayEn_wt            = RF_DRIVER_DELAYEN_WT; 
      rfDriver.delayDisable_wt       = RF_DRIVER_DELAYDIS_WT;
      rfDriver.delayLow              = RF_DRIVER_DELAYLOW;
      rfDriver.delayHigh             = RF_DRIVER_DELAYHIGH;
      rfDriver.setCallbacks(scoreboard.rfDriverCbs);

    ibMonitor   = new ("IB Monitor", miGenerator.transMbx, dmaModul, IB);
      ibMonitor.setCallbacks(scoreboard.monitorCbs);
      ibMonitor.setCheckerCallbacks(checker.monitorCbs);
//      coverage.addInternalBusInterface (IB,"IB Coverage");

    refModel   = new ("Reference Model", timeoutModule, RX_SU, TX_SU, 
                      MISC, IB, MI32, DMA);
        
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
  // Initialize design
  task initDesign();
    const int PAC_DDM_ADDR = 'h2200000;

    MISC.misc_cb.INIT <= '1;
    #(CLK_PERIOD);
    miDriver.setEnabled();

    // Run generators
    miGenerator.setEnabled(2+FLOWS);

    for(int i=0;i<FLOWS; i++)
      ibMonitor.readRequest(PAC_DDM_ADDR + i*'h2000 + 'h08);

    // While generator is active do nothing
    while (miGenerator.enabled)
      #(CLK_PERIOD);

    // Wait after initialisation
    #(5*CLK_PERIOD);

    MISC.misc_cb.INIT <= 0;

  endtask: initDesign  

  // --------------------------------------------------------------------------
  // Enable test Environment
  task enableTestEnvironment();
    // Enable Driver, Monitor, Coverage for each port 
    miscDriver.setEnabled();
    txSuDriver.setEnabled();
    rxSuDriver.setEnabled();
    rfDriver.setEnabled();
    ibMonitor.setEnabled();
    dmaModul.setEnabled();
    timeoutModule.setEnabled();
    refModel.setEnabled();
//    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
    int i = 0;

    // Disable drivers
    #(5000*CLK_PERIOD); 
    txSuDriver.setDisabled();
    rxSuDriver.setDisabled();
    rfDriver.setDisabled();
    miDriver.setDisabled();

    // Set Flush to get remaining packets
    miscDriver.setFlush();

    // Check if monitors are not receiving transaction for 5000 CLK_PERIODs
    while (i<5000) begin
      if (ibMonitor.busy) i = 0;
      else i++;
      #(CLK_PERIOD); 
    end

    miscDriver.setDisabled();
    ibMonitor.setDisabled();
    dmaModul.setDisabled();
    timeoutModule.setDisabled();
    refModel.setDisabled();
//    coverage.setDisabled();
  endtask : disableTestEnvironment

  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Test Case 1
  task test1();
    $write("\n\n############ TEST CASE 1 ############\n\n");
    // Initialize DUT
    initDesign();

    // Enable Test environment
    enableTestEnvironment();

    // Run generators
    txSuGenerator.setEnabled(TX_STATUS_UPDATE_COUNT);
    rxSuGenerator.setEnabled(RX_STATUS_UPDATE_COUNT);
    rfGenerator.setEnabled();

    // While generator is active do nothing
    while (txSuGenerator.enabled || rxSuGenerator.enabled)
      #(CLK_PERIOD);
    
    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard and Checker
    scoreboard.display();
    checker.display();
//    coverage.display();
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
    $write("FLOWS:\t\t%0d\nBLOCK_SIZE:\t\t%0d\nBASE_ADDR:\t\t%0x\nDMA_ID:\t\t%0d\nDMA_DATA_WIDTH:\t%0d\nNFIFO_LUT_MEMORY:\t%0d\n",FLOWS,BLOCK_SIZE,BASE_ADDR,DMA_ID,DMA_DATA_WIDTH,NFIFO_LUT_MEMORY);
    
    test1();       // Run Test 1
    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $stop();       // Stop testing
  end

endprogram

