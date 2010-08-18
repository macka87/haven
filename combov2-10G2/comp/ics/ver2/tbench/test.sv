/* \file test.sv
 * \brief DMA Module automatic test
 * \author Marek Santa <xsanta06@stud.fit.vutbr.cz> 
 * \date 2009 
 */
/*
 * Copyright (C) 2009 CESNET
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
 * $Id: test.sv 14268 2010-07-08 14:33:09Z xkoran01 $
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import sv_fl_pkg::*;
import sv_dmamodule_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic                CLK,
  input  logic                RX_INTERRUPT,
  input  logic                TX_INTERRUPT,
  output logic                RESET,
  iInternalBusUp.ib_up_tb     IBUP,
  iInternalBusDown.ib_down_tb IBDOWN,
  iFrameLinkRx.tb             FLRX[FLOWS],
  iFrameLinkTx.tb             FLTX[FLOWS],
  iFrameLinkTx.monitor        MONITOR[FLOWS]
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  
  //! Transaction
  FrameLinkTransaction      flBlueprint; 
  //! RX generator                            
  Generator                 rxGenerator[FLOWS];
  //! TX generator                            
  Generator                 txGenerator;
  //! Scoreboards  
  Scoreboard #(FLOWS, 1)    rxScoreboard, txScoreboard; 
  //! FrameLink driver                               
  FrameLinkDriver    #(DRIVER0_DATA_WIDTH, DRIVER0_DREM_WIDTH)   flDriver[FLOWS];
  //! FrameLink monitor      
  FrameLinkMonitor   #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) flMonitor[FLOWS]; 
  //! FrameLink Responder     
  FrameLinkResponder #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) flResponder[FLOWS];
  //! RAM memory
  DmaModuleSW        #(IBWIDTH, FLOWS, PAGE_SIZE, PAGE_COUNT)    ram;
  //! Internal Bus Upstream
  IbUpstream         #(IBWIDTH, FLOWS, PAGE_SIZE, PAGE_COUNT)    ibUpstream;
  //! Internal Bus Downstream
  IbDownstream       #(IBWIDTH, FLOWS, PAGE_SIZE, PAGE_COUNT)    ibDownstream;
  //! RAM driver
  RamDriver          #(IBWIDTH, FLOWS, PAGE_SIZE, PAGE_COUNT)    ramDriver;
  //! RAM monitor
  RamMonitor         #(IBWIDTH, FLOWS, PAGE_SIZE, PAGE_COUNT)    ramMonitor;
  // Coverage                             
//  Coverage #(DRIVER0_DATA_WIDTH, CTRL_DMA_DATA_WIDTH, MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) coverage; 
  
  // Virtual interfaces
  virtual iFrameLinkRx.tb #(DRIVER0_DATA_WIDTH, DRIVER0_DREM_WIDTH) vFLRX[FLOWS];
  virtual iFrameLinkTx.tb #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) vFLTX[FLOWS];
  virtual iFrameLinkTx.monitor #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) vMONITOR[FLOWS];
  
  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // -- Create Environment ----------------------------------------------------
  //! Create Environment
  /*!
   * Function is responsible for instantiate all used classes and initiate their
   * attributes.          
   */
  task createEnvironment();  
    // Create generators    
    if (FLOWS == 1) begin
      rxGenerator[0]= new("RX GENERATOR", 0);
      flBlueprint = new;
      flBlueprint.packetCount   = GENERATOR_PACKET_COUNT;
      flBlueprint.packetSizeMax = GENERATOR_PACKET_SIZE_MAX;
      flBlueprint.packetSizeMin = GENERATOR_PACKET_SIZE_MIN;
      rxGenerator[0].blueprint = flBlueprint;
    end
    else begin
      for(int i=0; i<FLOWS; i++) begin
        string generatorLable;
        $swrite(generatorLable, "RX Generator %0d", i);
        rxGenerator[i]= new(generatorLable, i);
        flBlueprint = new;
        flBlueprint.packetCount   = GENERATOR_PACKET_COUNT;
        flBlueprint.packetSizeMax = GENERATOR_PACKET_SIZE_MAX;
        flBlueprint.packetSizeMin = GENERATOR_PACKET_SIZE_MIN;
        rxGenerator[i].blueprint = flBlueprint;
      end
    end  
    
    txGenerator = new ("TX Generator", 0);
    flBlueprint = new;
    flBlueprint.packetCount   = GENERATOR_PACKET_COUNT;
    flBlueprint.packetSizeMax = GENERATOR_PACKET_SIZE_MAX;
    flBlueprint.packetSizeMin = GENERATOR_PACKET_SIZE_MIN;
    txGenerator.blueprint = flBlueprint;

    // Assign virtual interfaces
    vFLRX    = FLRX;
    vFLTX    = FLTX;
    vMONITOR = MONITOR;

    // Create scoreboard
    rxScoreboard = new("RX");   
    txScoreboard = new("TX");  
    
    // Create RAM
    ram = new();
    
    // Create IbusUpstream
    ibDownstream = new (IBDOWN, ram);
    
    // Create IbusUpstream
    ibUpstream = new (IBUP, ram, ibDownstream);
    
    // Create RAM driver
    ramDriver = new ("RamDriver", txGenerator.transMbx, ram, ibUpstream,ibDownstream);
      ramDriver.setCallbacks(txScoreboard.driverCbs);
      ramDriver.txPauseAllowed        = TX_PAUSE_ALLOWED; 
      ramDriver.txPauseAll            = TX_PAUSE_ALL;
      ramDriver.pauseDelayLow         = PAUSE_DELAYLOW;
      ramDriver.pauseDelayHigh        = PAUSE_DELAYHIGH;
      ramDriver.insidePauseDelayLow   = INSIDE_PAUSE_DELAYLOW;
      ramDriver.insidePauseDelayHigh  = INSIDE_PAUSE_DELAYHIGH;
      ramDriver.txStopAllowed         = TX_STOP_ALLOWED; 
      ramDriver.txStopAll             = TX_STOP_ALL;
      ramDriver.stopDelayLow          = STOP_DELAYLOW;
      ramDriver.stopDelayHigh         = STOP_DELAYHIGH;
      ramDriver.insideStopDelayLow    = INSIDE_STOP_DELAYLOW;
      ramDriver.insideStopDelayHigh   = INSIDE_STOP_DELAYHIGH;
    
    // Create RAM monitor
    ramMonitor = new ("RamMonitor", ram, ibUpstream, ibDownstream);
      ramMonitor.setCallbacks(rxScoreboard.monitorCbs);
      ramMonitor.rxPauseAllowed        = RX_PAUSE_ALLOWED; 
      ramMonitor.rxPauseAll            = RX_PAUSE_ALL;
      ramMonitor.pauseDelayLow         = PAUSE_DELAYLOW;
      ramMonitor.pauseDelayHigh        = PAUSE_DELAYHIGH;
      ramMonitor.insidePauseDelayLow   = INSIDE_PAUSE_DELAYLOW;
      ramMonitor.insidePauseDelayHigh  = INSIDE_PAUSE_DELAYHIGH;
      ramMonitor.rxStopAllowed         = RX_STOP_ALLOWED; 
      ramMonitor.rxStopAll             = RX_STOP_ALL;
      ramMonitor.stopDelayLow          = STOP_DELAYLOW;
      ramMonitor.stopDelayHigh         = STOP_DELAYHIGH;
      ramMonitor.insideStopDelayLow    = INSIDE_STOP_DELAYLOW;
      ramMonitor.insideStopDelayHigh   = INSIDE_STOP_DELAYHIGH;
    
    // Create FL driver    
    for (int i=0; i<FLOWS; i++)
    begin
      string driverLabel;
      $swrite(driverLabel, "Driver%0d", i);
      flDriver[i] = new (driverLabel, rxGenerator[i].transMbx, vFLRX[i]);

      flDriver[i].setCallbacks(rxScoreboard.driverCbs);
      flDriver[i].txDelayEn_wt            = DRIVER0_DELAYEN_WT; 
      flDriver[i].txDelayDisable_wt       = DRIVER0_DELAYDIS_WT;
      flDriver[i].txDelayLow              = DRIVER0_DELAYLOW;
      flDriver[i].txDelayHigh             = DRIVER0_DELAYHIGH;
      flDriver[i].insideTxDelayEn_wt      = DRIVER0_INSIDE_DELAYEN_WT; 
      flDriver[i].insideTxDelayDisable_wt = DRIVER0_INSIDE_DELAYDIS_WT;
      flDriver[i].insideTxDelayLow        = DRIVER0_INSIDE_DELAYLOW;
      flDriver[i].insideTxDelayHigh       = DRIVER0_INSIDE_DELAYHIGH;    
    end    
    
    // Create FL monitor  
    for (int i=0; i<FLOWS; i++)
    begin  
      string monitorLabel;
      $swrite(monitorLabel, "Monitor%0d", i);
      flMonitor[i] = new (monitorLabel, vMONITOR[i]);

      flMonitor[i].setCallbacks(txScoreboard.monitorCbs);
    end
    
    // Create responder
    for (int i=0; i<FLOWS; i++)
    begin
      string responderLabel;
      $swrite(responderLabel, "Responder%0d", i);
      flResponder[i] = new (responderLabel, vFLTX[i]);

      flResponder[i].rxDelayEn_wt            = MONITOR0_DELAYEN_WT; 
      flResponder[i].rxDelayDisable_wt       = MONITOR0_DELAYDIS_WT;
      flResponder[i].rxDelayLow              = MONITOR0_DELAYLOW;
      flResponder[i].rxDelayHigh             = MONITOR0_DELAYHIGH;
      flResponder[i].insideRxDelayEn_wt      = MONITOR0_INSIDE_DELAYEN_WT; 
      flResponder[i].insideRxDelayDisable_wt = MONITOR0_INSIDE_DELAYDIS_WT;
      flResponder[i].insideRxDelayLow        = MONITOR0_INSIDE_DELAYLOW;
      flResponder[i].insideRxDelayHigh       = MONITOR0_INSIDE_DELAYHIGH;    
    end    
/*    
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
*/        
  endtask : createEnvironment

  // --------------------------------------------------------------------------
  //                       Test auxilarity procedures
  // --------------------------------------------------------------------------
  
  // -- Reset Design ----------------------------------------------------------
  //! Resets design
  task resetDesign();
    RESET=1;                       // Init Reset variable
    #RESET_TIME     RESET = 0;     // Deactivate reset after reset_time
  endtask : resetDesign

  // -- Enable Test Environment -----------------------------------------------
  //! Enable Test Environment
  /*!
   * Function enables all drivers, monitors and coverages.          
   */
  task enableTestEnvironment();
    // Enable drivers
    for(int i=0; i<FLOWS; i++)
      flDriver[i].setEnabled();
      
    ramDriver.setEnabled();  
    ibDownstream.setEnabled();

    // Enable monitors
    for(int i=0; i<FLOWS; i++)
    begin
      flMonitor[i].setEnabled();
      flResponder[i].setEnabled();
    end
    
    ramMonitor.setEnabled();
    ibUpstream.setEnabled();
    
    // Enable coverage
   // coverage.setEnabled();
  endtask : enableTestEnvironment

  // -- Disable Test Environment ----------------------------------------------
  //! Disable Test Environment
  /*!
   * Function disables all drivers, monitors and coverages.          
   */
  task disableTestEnvironment();
     // Disable drivers
     #(3000*CLK_PERIOD);
     for(int i=0; i<FLOWS; i++)  
       flDriver[i].setDisabled();
      
     ramDriver.setDisabled(); 
     ibDownstream.setDisabled(); 
      
     // Disable monitors     
     #(1000*CLK_PERIOD);
     for (int i=0;i<FLOWS; i++)
     begin
       flMonitor[i].setDisabled();
       flResponder[i].setDisabled();
     end 
     
     ramMonitor.setDisabled(); 
     ibUpstream.setDisabled();
     
     // Disable coverage 
     //coverage.setDisabled();
  endtask : disableTestEnvironment

  task interrupts();
     for(int i = 0; i < FLOWS; i++)
     begin
        ibDownstream.setPtr('h102, 32'h00000814 + i*'h80);
        ibDownstream.setPtr('h102, 32'h00000854 + i*'h80);
     end

     while(1)
     begin
         wait(RX_INTERRUPT == 1 || TX_INTERRUPT == 1)
         if(TX_INTERRUPT == 1)
             ibDownstream.sendIntReq(1);
         else
             ibDownstream.sendIntReq(0);
         #(CLK_PERIOD);
     end
  endtask : interrupts

  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // -- Test Case 1 -----------------------------------------------------------
  //! Test Case 1
  /*!
   * Function is responsible for running test.          
   */
  task test1();
     $write("\n\n############ TEST CASE 1 ############\n\n");
     // Initialize DUT
     ibDownstream.initialization();
/*     fork
         interrupts();
     join_none;*/
     #(10*CLK_PERIOD);
     // Enable Test environment
     enableTestEnvironment();
     // Run generators
     #(1*CLK_PERIOD);
     for(int i=0; i<FLOWS; i++) 
       rxGenerator[i].setEnabled(RX_TRANSACTION_COUNT);
     
     txGenerator.setEnabled(TX_TRANSACTION_COUNT);
     

     // While generator is active do nothing
     if (FLOWS == 1) wait (rxGenerator[0].enabled == 0);
     else begin
       for(int i=0; i<FLOWS; i++)  
         wait (rxGenerator[i].enabled == 0);
     end    
     
     wait (txGenerator.enabled == 0);
    
     // Disable Test Enviroment
     disableTestEnvironment();

     // Display Scoreboard
     rxScoreboard.display();
     txScoreboard.display();
//     coverage.display();
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
    test1();       // Run Test 1

    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $stop();       // Stop testing
  end

endprogram

