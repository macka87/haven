/*
 * test.sv: RX DMA Controller automatic test
 * Copyright (C) 2008 CESNET
 * Author(s): Marcela Šimková <xsimko03@stud.fit.vutbr.cz>
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
import sv_rx_dma_ctrl_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic         CLK,
  output logic         RESET,
  iMi32.tb             SW,
  iInternalBus.ib_read_tb IB,
  iDmaCtrl.misc_tb   MISC[BUFFER_FLOWS],
  iDmaCtrl.desc_tb   DESC[BUFFER_FLOWS],
  iDmaCtrl.dma_tb    DMA[BUFFER_FLOWS],
  iFrameLinkRx.tb    FL[BUFFER_FLOWS]
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  
  // FrameLink Transactions
  FrameLinkTransaction                                                                          flBlueprint; 
  // Software Modul
  RxSoftwareModul #(BUFFER_FLOWS, PAGE_SIZE, PAGE_COUNT)                                        swModul; 
  // Descriptor Manager Modul
  RxDescManager #(CTRL_DMA_DATA_WIDTH,BUFFER_FLOWS, PAGE_SIZE, PAGE_COUNT)                      descMan[BUFFER_FLOWS];
  // Generator for one flow (problems with ModelSim)
  //Generator                                                                                   generator;
  // Generator for more flows
  Generator                                                                                     generator[BUFFER_FLOWS];
  // Driver                               
  FrameLinkDriver #(DRIVER0_DATA_WIDTH, RXDREMWIDTH, BUFFER_FLOWS, PAGE_SIZE, PAGE_COUNT)       flDriver[BUFFER_FLOWS]; 
  // Monitor      
  RxDmaCtrlMonitor #(MONITOR0_DATA_WIDTH, CTRL_DMA_DATA_WIDTH, BUFFER_FLOWS, PAGE_SIZE, PAGE_COUNT) rxMonitor; 
  // InternalBus Modul
  RxIbusModul #(MONITOR0_DATA_WIDTH, CTRL_DMA_DATA_WIDTH, BUFFER_FLOWS, PAGE_SIZE, PAGE_COUNT)  ibModul;
  // Scoreboard  
  Scoreboard                                                                   		        rxScoreboard; 
  // Coverage                             
  Coverage #(RXDWIDTH, RXDREMWIDTH, CTRL_DMA_DATA_WIDTH, BUFFER_DATA_WIDTH)                                                                                     coverage; 
  
  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createEnvironment();  
    swModul = new("Inicialization",SW);
    descMan[0] = new("DescManager0", DESC[0], 0);
    descMan[1] = new("DescManager1", DESC[1], 1);
    descMan[2] = new("DescManager0", DESC[2], 2);
    descMan[3] = new("DescManager1", DESC[3], 3);

    //Create generators for one flow
    /*generator= new("Generator", 0);
    flBlueprint = new;
    flBlueprint.packetCount   = GENERATOR_PACKET_COUNT;
    flBlueprint.packetSizeMax = GENERATOR_PACKET_SIZE_MAX;
    flBlueprint.packetSizeMin = GENERATOR_PACKET_SIZE_MIN;
    assert(flBlueprint.randomize());
    generator.blueprint = flBlueprint;*/

    // Create generators for more flows
    for(int i=0; i<BUFFER_FLOWS; i++) begin
      generator[i]= new("Generator", i);
      flBlueprint = new;
      flBlueprint.packetCount   = GENERATOR_PACKET_COUNT;
      flBlueprint.packetSizeMax = GENERATOR_PACKET_SIZE_MAX;
      flBlueprint.packetSizeMin = GENERATOR_PACKET_SIZE_MIN;
      assert(flBlueprint.randomize());
      generator[i].blueprint = flBlueprint;
    end;
        
    // Create scoreboard
    rxScoreboard = new();
    
    // Create driver for one flow
    /*flDriver[0]    = new ("Driver0", 0, generator.transMbx, FL[0], rxScoreboard.transInfoMbx);*/

    // Create drivers for more flows
    flDriver[0]    = new ("Driver0", 0, generator[0].transMbx, FL[0], rxScoreboard.transInfoMbx);
    flDriver[1]    = new ("Driver1", 1, generator[1].transMbx, FL[1], rxScoreboard.transInfoMbx);
    flDriver[2]    = new ("Driver2", 2, generator[2].transMbx, FL[2], rxScoreboard.transInfoMbx);
    flDriver[3]    = new ("Driver3", 3, generator[3].transMbx, FL[3], rxScoreboard.transInfoMbx);
    
    for(int i=0; i<BUFFER_FLOWS; i++) begin
      flDriver[i].rxDelayEn_wt             = DRIVER0_DELAYEN_WT; 
      flDriver[i].rxDelayDisable_wt        = DRIVER0_DELAYDIS_WT;
      flDriver[i].rxDelayLow               = DRIVER0_DELAYLOW;
      flDriver[i].rxDelayHigh              = DRIVER0_DELAYHIGH;
      flDriver[i].insideRxDelayEn_wt       = DRIVER0_INSIDE_DELAYEN_WT; 
      flDriver[i].insideRxDelayDisable_wt  = DRIVER0_INSIDE_DELAYDIS_WT;
      flDriver[i].insideRxDelayLow         = DRIVER0_INSIDE_DELAYLOW;
      flDriver[i].insideRxDelayHigh        = DRIVER0_INSIDE_DELAYHIGH;
      flDriver[i].setCallbacks(rxScoreboard.driverCbs);
    end
      
    // Create monitor
    ibModul = new ("ibModul0",IB,DMA);
    rxMonitor = new ("Monitor0",ibModul,SW,rxScoreboard.transInfoMbx);
      //rxMonitor.reqDelayEn_wt             = MONITOR0_REQDELAYEN_WT;
      //rxMonitor.reqDelayDisable_wt        = MONITOR0_REQDELAYDIS_WT;
      //rxMonitor.reqDelayLow               = MONITOR0_REQDELAYLOW;
      //rxMonitor.reqDelayHigh              = MONITOR0_REQDELAYHIGH;
      rxMonitor.setCallbacks(rxScoreboard.monitorCbs);
     
    // Coverage class
    coverage = new();
      coverage.addFrameLinkInterface (FL[0],"FLcoverage0");
      coverage.addFrameLinkInterface (FL[1],"FLcoverage1");
      coverage.addFrameLinkInterface (FL[2],"FLcoverage2");
      coverage.addFrameLinkInterface (FL[3],"FLcoverage3");
      coverage.addDmaInterface (DMA[0],"DMAModulcoverage0");
      coverage.addDmaInterface (DMA[1],"DMAModulcoverage1");  
      coverage.addDmaInterface (DMA[2],"DMAModulcoverage2");
      coverage.addDmaInterface (DMA[3],"DMAModulcoverage3");
      coverage.addDescriptorInterface (DESC[0],"DESCcoverage0");
      coverage.addDescriptorInterface (DESC[1],"DESCcoverage1"); 
      coverage.addDescriptorInterface (DESC[2],"DESCcoverage2");
      coverage.addDescriptorInterface (DESC[3],"DESCcoverage3");
      coverage.addInternalBusInterface (IB,"IBModulcoverage");
      coverage.addSoftwareInterface (SW,"SWModulcoverage");
         
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
    // Enable Driver, Monitor, Descriptor Manager Modul, InternalBus Modul, Coverage for each port
    for(int i=0; i<BUFFER_FLOWS; i++) begin
      flDriver[i].setEnabled();
      descMan[i].setEnabled();
    end
    rxMonitor.setEnabled();
    ibModul.setEnabled();
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
     // Disable drivers
     #(1000*CLK_PERIOD); 
     for(int i=0; i<BUFFER_FLOWS; i++)
       flDriver[i].setDisabled();
     // Disable monitors
     #(10000*CLK_PERIOD);
     for(int i=0; i<BUFFER_FLOWS; i++) 
       descMan[i].setDisabled();
     rxMonitor.setDisabled();
     ibModul.setDisabled();
     coverage.setDisabled();
  endtask : disableTestEnvironment

  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Test Case 1
  task test1();
     $write("\n\n############ TEST CASE 1 ########################\n\n");
     // Enable Test environment
     swModul.initCtrl();            // Wait until swModul finishes initialization
     
     descMan[0].addDescriptor(0);
     descMan[1].addDescriptor(PAGE_SIZE);
     descMan[2].addDescriptor(2*PAGE_SIZE);
     descMan[3].addDescriptor(3*PAGE_SIZE);
     
     enableTestEnvironment();
     
     // Run generator for one flow
     //generator.setEnabled(TRANSACTION_COUNT);

     // Run generators for more flows
     for(int i=0; i<BUFFER_FLOWS; i++) begin  
       generator[i].setEnabled(TRANSACTION_COUNT);
     end

     // Do nothing if the generator is enabled (for one flow)
     //while (generator.enabled)
     //  #(CLK_PERIOD);

     // Do nothing if the generators are enabled (for more flows)
     for(int i=0; i<BUFFER_FLOWS; i++) begin  
       while (generator[i].enabled)
         #(CLK_PERIOD);
     end 
     
     // Disable Test Enviroment
     disableTestEnvironment();

     // Display Scoreboard
     rxScoreboard.display();
     coverage.display();
     
  endtask: test1
 
  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    // -------------------------------------
    // DESIGN ENVIROMENT
    // -------------------------------------
    resetDesign();              // Reset design
    #(10*CLK_PERIOD);
    createEnvironment();        // Create Test Enviroment
    
    // -------------------------------------
    // TESTING
    // -------------------------------------
    $write("\n\n############ GENERICS AND PARAMETERS ############\n\n");
    $write("------------ DUT GENERICS ---------------------\n\n");
    $write("BUFFER_DATA_WIDTH:\t%1d\nBUFFER_FLOWS:\t%1d\nBUFFER_BLOCK_SIZE:\t%1d\nBUFFER_TOTAL_FLOW_SIZE:\t%1d\nCTRL_BUFFER_ADDR:\t%1d\nCTRL_DMA_DATA_WIDTH:\t%1d\n",BUFFER_DATA_WIDTH,BUFFER_FLOWS,BUFFER_BLOCK_SIZE,BUFFER_TOTAL_FLOW_SIZE,CTRL_BUFFER_ADDR,CTRL_DMA_DATA_WIDTH);
    $write("\n------------ RAM PARAMETERS -------------------\n\n");
    $write("PAGE_SIZE:\t%1d\nPAGE_COUNT:\t%1d\n",PAGE_SIZE,PAGE_COUNT);
    $write("\n------------ TRANSACTION PARAMETERS------------\n\n");
    $write("TRANSACTION_COUNT:\t%1d\n",TRANSACTION_COUNT);

    test1();                    // Run Test 1
    
    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $stop();                    // Stop testing
  end

endprogram

