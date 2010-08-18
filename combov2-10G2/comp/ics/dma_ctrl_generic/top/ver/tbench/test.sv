/* \file test.sv
 * \brief DMA Module Generic automatic test
 * \author Marek Santa <santa@liberouter.org> 
 * \date 2010
 */
/*
 * Copyright (C) 2010 CESNET
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
 * $Id: test.sv 15016 2010-08-12 12:32:34Z xsanta06 $
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import sv_fl_pkg::*;
import sv_mi32_pkg::*;
import sv_discard_stat_pkg::*;
import sv_dma_module_gen_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic                CLK,
  output logic                RESET,
  input  logic                RX_INTERRUPT,
  input  logic                TX_INTERRUPT,
  iInternalBusUp.ib_up_tb     IBUP,
  iInternalBusDown.ib_down_tb IBDOWN,
  iFrameLinkRx.tb             RX_DRIV[RX_IFC_COUNT],
  iFrameLinkTx.tb             TX_MUX[RX_IFC_COUNT],
  iFrameLinkRx.tb             FLRX,
  iFrameLinkTx.tb             FLTX[TX_IFC_COUNT],
  iFrameLinkTx.monitor        MONITOR[TX_IFC_COUNT],
  iMi32.tb                    MI,
  iDiscardStat.rx_tb          DS,
  iDiscardStat.stat_tb        STAT
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  
  //! Transaction
  FrameLinkTransaction      flBlueprint; 
  //! RX generator                            
  Generator                 rxGenerator[RX_IFC_COUNT];
  //! TX generator                            
  Generator                 txGenerator;
  //! FrameLink driver                               
  FrameLinkDriver    #(DRIVER0_DATA_WIDTH, DRIVER0_DREM_WIDTH)   
                                                     flDriver[RX_IFC_COUNT];
  //! FrameLink Multiplexor
  FrameLinkMultiplexor #(DRIVER0_DATA_WIDTH, DRIVER0_DREM_WIDTH,
                                    RX_IFC_COUNT, STATUSWIDTH)   flMultiplexor;
  //! FrameLink monitor      
  FrameLinkMonitor   #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) 
                                                     flMonitor[TX_IFC_COUNT]; 
  //! FrameLink Responder     
  FrameLinkResponder #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) 
                                                     flResponder[TX_IFC_COUNT];
  //! RAM memory
  DmaModuleSW        #(IBWIDTH, FLOWS, PAGE_SIZE, PAGE_COUNT)    ram;
  //! MI32 Module
  Mi32Module         #(RX_IFC_COUNT, TX_IFC_COUNT, PAGE_SIZE, PAGE_COUNT) 
                                                                 miModule;
  // Discarding Model
  DmaDiscardingModel #(DRIVER0_DATA_WIDTH, DRIVER0_DREM_WIDTH, 
                                  RX_IFC_COUNT, STATUSWIDTH)    discardingModel;
  //! Internal Bus Upstream
  IbUpstream         #(IBWIDTH, FLOWS, PAGE_SIZE, PAGE_COUNT)    ibUpstream;
  //! Internal Bus Downstream
  IbDownstream       #(IBWIDTH, FLOWS, PAGE_SIZE, PAGE_COUNT)    ibDownstream;
  //! RAM driver
  RamDriver          #(IBWIDTH, FLOWS, RX_IFC_COUNT, TX_IFC_COUNT, 
                                       PAGE_SIZE, PAGE_COUNT)    ramDriver;
  //! RAM monitor
  RamMonitor         #(IBWIDTH, FLOWS, RX_IFC_COUNT, TX_IFC_COUNT, 
                                       PAGE_SIZE, PAGE_COUNT)    ramMonitor;
  //! RX Scoreboard  
  Scoreboard         #(RX_IFC_COUNT, TR_TABLE_FIRST_ONLY)        rxScoreboard; 
  //! TX Scoreboard
  Scoreboard         #(TX_IFC_COUNT, TR_TABLE_FIRST_ONLY)        txScoreboard; 
  
  // Virtual interfaces
  virtual iFrameLinkRx.tb #(DRIVER0_DATA_WIDTH, DRIVER0_DREM_WIDTH) 
                                                       vRX_DRIV[RX_IFC_COUNT];
  virtual iFrameLinkTx.tb #(DRIVER0_DATA_WIDTH, DRIVER0_DREM_WIDTH) 
                                                       vTX_MUX[RX_IFC_COUNT];
  virtual iFrameLinkTx.tb #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) 
                                                       vFLTX[TX_IFC_COUNT];
  virtual iFrameLinkTx.monitor #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) 
                                                       vMONITOR[TX_IFC_COUNT];
  
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
    if (RX_IFC_COUNT == 1) begin
      rxGenerator[0]= new("RX GENERATOR", 0);
      flBlueprint = new;
      flBlueprint.packetCount   = GENERATOR_PACKET_COUNT;
      flBlueprint.packetSizeMax = GENERATOR_PACKET_SIZE_MAX;
      flBlueprint.packetSizeMin = GENERATOR_PACKET_SIZE_MIN;
      rxGenerator[0].blueprint = flBlueprint;
    end
    else begin
      for(int i=0; i<RX_IFC_COUNT; i++) begin
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
    vRX_DRIV = RX_DRIV;
    vTX_MUX  = TX_MUX;
    vFLTX    = FLTX;
    vMONITOR = MONITOR;

    // Create scoreboard
    rxScoreboard = new("RX Scoreboard");   
    txScoreboard = new("TX Scoreboard");  
    
    // Create RAM
    ram = new();
    
    // Create discarding model
    discardingModel = new("Discarding Model", FLRX, DS, STAT);
      discardingModel.setCallbacks(rxScoreboard.driverCbs);

    // Create MI32 Module
    miModule = new("MI32 Module", MI);
    
    // Create IbusUpstream
    ibDownstream = new (IBDOWN, ram);
    
    // Create IbusUpstream
    ibUpstream = new (IBUP, ram, ibDownstream);
    
    // Create RAM driver
    ramDriver = new ("RamDriver", txGenerator.transMbx, ram, 
                      miModule, ibDownstream);
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
    ramMonitor = new ("RamMonitor", ram, miModule, ibDownstream);
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
    for (int i=0; i<RX_IFC_COUNT; i++)
    begin
      string driverLabel;
      $swrite(driverLabel, "Driver%0d", i);
      flDriver[i] = new (driverLabel, rxGenerator[i].transMbx, vRX_DRIV[i]);

      flDriver[i].setCallbacks(discardingModel.discardStatCbs);
      flDriver[i].txDelayEn_wt            = DRIVER0_DELAYEN_WT; 
      flDriver[i].txDelayDisable_wt       = DRIVER0_DELAYDIS_WT;
      flDriver[i].txDelayLow              = DRIVER0_DELAYLOW;
      flDriver[i].txDelayHigh             = DRIVER0_DELAYHIGH;
      flDriver[i].insideTxDelayEn_wt      = DRIVER0_INSIDE_DELAYEN_WT; 
      flDriver[i].insideTxDelayDisable_wt = DRIVER0_INSIDE_DELAYDIS_WT;
      flDriver[i].insideTxDelayLow        = DRIVER0_INSIDE_DELAYLOW;
      flDriver[i].insideTxDelayHigh       = DRIVER0_INSIDE_DELAYHIGH;    
    end    

    // Create FL multiplexor
    flMultiplexor = new ("Multiplexor", vTX_MUX, FLRX, DS);
      flMultiplexor.muxDelayLow           = MULTIPLEXOR_MUXDELAYLOW;
      flMultiplexor.muxDelayHigh          = MULTIPLEXOR_MUXDELAYHIGH;
    
    // Create FL monitor  
    for (int i=0; i<TX_IFC_COUNT; i++)
    begin  
      string monitorLabel;
      $swrite(monitorLabel, "Monitor%0d", i);
      flMonitor[i] = new (monitorLabel, vMONITOR[i]);

      flMonitor[i].setCallbacks(txScoreboard.monitorCbs);
    end
    
    // Create responder
    for (int i=0; i<TX_IFC_COUNT; i++)
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
    for(int i=0; i<RX_IFC_COUNT; i++)
      flDriver[i].setEnabled();
      
    flMultiplexor.setEnabled();
    ramDriver.setEnabled();  
    ibDownstream.setEnabled();
    miModule.setEnabled();

    if (RX_DISCARD_EN)
      discardingModel.setEnabled();

    // Enable monitors
    for(int i=0; i<TX_IFC_COUNT; i++)
    begin
      flMonitor[i].setEnabled();
      flResponder[i].setEnabled();
    end
    
    ramMonitor.setEnabled();
    ibUpstream.setEnabled();
  endtask : enableTestEnvironment

  // -- Disable Test Environment ----------------------------------------------
  //! Disable Test Environment
  /*!
   * Function disables all drivers, monitors and coverages.          
   */
  task disableTestEnvironment();
    int i, busy;

    // Disable drivers
    #(1000*CLK_PERIOD);
    for(int i=0; i<RX_IFC_COUNT; i++)  
      flDriver[i].setDisabled();
     
    flMultiplexor.setDisabled();
    ramDriver.setDisabled(); 
      
    // Check if monitors are not receiving transaction for 100 CLK_PERIODs
    i = 0;
    while (i<100) begin
      busy = 0;
      for (int j=0; j<TX_IFC_COUNT; j++)
        if (flMonitor[j].busy) busy = 1;
      if (busy) i=0;
      else i++;
      #(CLK_PERIOD); 
    end

    // Disable monitors     
    for (int i=0;i<TX_IFC_COUNT; i++)
    begin
      flMonitor[i].setDisabled();
      flResponder[i].setDisabled();
    end 

    if (RX_DISCARD_EN)
      discardingModel.setEnabled();
    
    miModule.setDisabled(); 
    ramMonitor.setDisabled(); 
    ibDownstream.setDisabled(); 
    ibUpstream.setDisabled();
    
    #(100*CLK_PERIOD);
  endtask : disableTestEnvironment

  // -- DUT Initialisation ----------------------------------------------------
  //! DUT Initialisation
  /*!
   * 1. Descriptor manager initialization
   * 2. Buffer Size Mask register initialization     
   * 3. Control register initialization     
   */
  task dutInitialisation();
    @(ibDownstream.ib_down.ib_down_cb);
    // Initialise Descriptor manager
    for(int i=0; i<RX_IFC_COUNT; i++)
      ibDownstream.initDescManagerRx(i, 1);

    for(int i=0; i<TX_IFC_COUNT; i++)
      ibDownstream.initDescManagerTx(i, 1);

    // Initialise Controllers
    miModule.initControllers();
    
  endtask : dutInitialisation

  // -- Check Frame Counters --------------------------------------------------
  //! Check Frame Counters
  /*!
   * Function check values of frame counters.          
   */
  task checkFrameCounters();
    bit [63:0] droppedFrames[RX_IFC_COUNT];
    bit [63:0] droppedLength[RX_IFC_COUNT];
    longint unsigned droppedFr[RX_IFC_COUNT]; //Dropped Frames Counter
    longint unsigned passedFr[RX_IFC_COUNT];  //Passed Frames Counter
    longint unsigned droppedLen[RX_IFC_COUNT];//Length of Dropped Frames Counter
    longint unsigned passedLen[RX_IFC_COUNT]; //Length of Passed Frames Counter

    miModule.readFrameCounters(droppedFrames, droppedLength);

    discardingModel.getStats(droppedFr, passedFr, droppedLen, passedLen);

    for (int i=0; i<RX_IFC_COUNT; i++) begin
      if ((droppedFrames[i] != droppedFr[i]) ||
          (droppedLength[i] != droppedLen[i])) begin
        // Display counters values
        $write("------------------------------------------------------------\n");
        $write("-- Channel %0d Frame Counters mismatch\n", i);
        $write("------------------------------------------------------------\n");
        if (droppedFrames[i] != droppedFr[i])
          $write("Dropped Frames does not match! Expected:%10d, Received:%10d\n",
                  droppedFr[i], droppedFrames[i]);
        if (droppedLength[i] != droppedLen[i])
          $write("Dropped Length does not match! Expected:%10d, Received:%10d\n",
                  droppedLen[i], droppedLength[i]);
        $write("------------------------------------------------------------\n");
      end
    end

  endtask : checkFrameCounters

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
     dutInitialisation();
     #(10*CLK_PERIOD);
     // Enable Test environment
     enableTestEnvironment();

     // Run generators
     #(900*CLK_PERIOD);
     for(int i=0; i<RX_IFC_COUNT; i++) 
       rxGenerator[i].setEnabled(RX_TRANSACTION_COUNT);
     
     txGenerator.setEnabled(TX_TRANSACTION_COUNT);
     
     // While generator is active do nothing
     if (RX_IFC_COUNT == 1) wait (rxGenerator[0].enabled == 0);
     else begin
       for(int i=0; i<RX_IFC_COUNT; i++)  
         wait (rxGenerator[i].enabled == 0);
     end    
     
     wait (txGenerator.enabled == 0);
    
     // Disable Test Enviroment
     disableTestEnvironment();

     // Display Scoreboard
     rxScoreboard.display();
     txScoreboard.display();

     // Check Frames Counters
     if (RX_DISCARD_EN)
       checkFrameCounters();
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

