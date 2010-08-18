/*
 * test.sv: RX DMA Controller automatic test
 * Copyright (C) 2009 CESNET
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
 * $Id: test.sv 10127 2009-08-06 11:17:41Z xsimko03 $
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import sv_rx_pac_dma_ctrl_pkg::*;
import test_pkg::*;
import sv_fl_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic                  CLK,
  output logic                  RESET,
  iPacDmaCtrl.misc_tb           PACDMA,
  iPacDmaCtrl.desc_tb           DESC,
  iDmaCtrl.dma_tb               DMA,
  iPacDmaCtrl.statrx_tb         STAT,
  iInternalBus.ib_read_tb       IB,
  iFrameLinkRx.tb               FL[FLOWS]
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  
  // FrameLink Transactions
  FrameLinkTransaction                                                                          flBlueprint; 
  // Generator for one flow (problems with ModelSim)
  //Generator                                                                                     generator;
  // Generator for more flows
  Generator                                                                                     generator[FLOWS];
  // Driver                               
  FrameLinkDriver #(DRIVER0_DATA_WIDTH, RXDREMWIDTH)                                            flDriver[FLOWS]; 
  // Monitor      
  RxDmaCtrlMonitor #(NUM_FLAGS, BUFFER_DATA_WIDTH, CTRL_DMA_DATA_WIDTH, FLOWS, 
                     RAM_SIZE, CTRL_DMA_ID, TRANS_TYPE)                                         rxMonitor; 
  // Descriptor Manager Modul
  RxDescManager #(FLOWS, RAM_SIZE, MAX_SIZE_OF_PACKET, BUFFER_DATA_WIDTH)                       descMan;
  // Status Update Manager Modul
  RxStatusManager #(FLOWS, NUM_FLAGS)                                                           status;
  // InternalBus Modul
  RxIbusModul #(MONITOR0_DATA_WIDTH, CTRL_DMA_DATA_WIDTH, FLOWS, RAM_SIZE, CTRL_DMA_ID,
                TRANS_TYPE)                                                                     ibModul;
  // DMA modul
  DmaModul #(CTRL_DMA_DATA_WIDTH, CTRL_DMA_ID, TRANS_TYPE)                                      dmaModul;
  // Scoreboard  
  Scoreboard #(FLOWS, 1)                                                       		        rxScoreboard; 
  // Coverage                             
  RxCoverage #(DRIVER0_DATA_WIDTH, RXDREMWIDTH, CTRL_DMA_DATA_WIDTH, BUFFER_DATA_WIDTH, FLOWS)  coverage; 
  
  // Only array of virtual interfaces can be indexed
  virtual iFrameLinkRx.tb #(DRIVER0_DATA_WIDTH, RXDREMWIDTH) vRX[FLOWS];
  
                                                                                  
  
  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createEnvironment();  
    descMan = new("DescManager0", DESC);
    status = new("StatManager0", STAT);
    
    //Create generators for one flow
    /*generator= new("Generator", 0);
    flBlueprint = new;
    flBlueprint.packetCount   = GENERATOR_PACKET_COUNT;
    flBlueprint.packetSizeMax = GENERATOR_PACKET_SIZE_MAX;
    flBlueprint.packetSizeMin = GENERATOR_PACKET_SIZE_MIN;
    assert(flBlueprint.randomize());
    generator.blueprint = flBlueprint;*/

    // Create generators for more flows
    for(int i=0; i<FLOWS; i++) begin
      generator[i]= new("Generator", i);
      flBlueprint = new;
      flBlueprint.packetCount   = GENERATOR_PACKET_COUNT;
      flBlueprint.packetSizeMax = GENERATOR_PACKET_SIZE_MAX;
      flBlueprint.packetSizeMin = GENERATOR_PACKET_SIZE_MIN;
      generator[i].blueprint = flBlueprint;
    end;
        
    // Assign virtual interfaces
    vRX = FL;
            
    // Create scoreboard
    rxScoreboard = new("RX");
    
    // Create driver
    for (int i=0; i<FLOWS; i++)
    begin
      string driverLabel;
    
      $swrite(driverLabel, "Driver %0d", i);
      flDriver[i]   = new (driverLabel, generator[i].transMbx, vRX[i]);
      //flDriver[i]   = new (driverLabel, generator.transMbx, vRX[i]);
      
      flDriver[i].txDelayEn_wt             = DRIVER0_DELAYEN_WT; 
      flDriver[i].txDelayDisable_wt        = DRIVER0_DELAYDIS_WT;
      flDriver[i].txDelayLow               = DRIVER0_DELAYLOW;
      flDriver[i].txDelayHigh              = DRIVER0_DELAYHIGH;
      flDriver[i].insideTxDelayEn_wt       = DRIVER0_INSIDE_DELAYEN_WT; 
      flDriver[i].insideTxDelayDisable_wt  = DRIVER0_INSIDE_DELAYDIS_WT;
      flDriver[i].insideTxDelayLow         = DRIVER0_INSIDE_DELAYLOW;
      flDriver[i].insideTxDelayHigh        = DRIVER0_INSIDE_DELAYHIGH;
      flDriver[i].setCallbacks(rxScoreboard.driverCbs);    
    end
    
    // Create monitor
    dmaModul  = new ("dmaModul0", DMA);
    ibModul = new ("ibModul0",dmaModul,IB);
    rxMonitor = new ("Monitor0",descMan,status,ibModul);
      //rxMonitor.reqDelayEn_wt             = MONITOR0_REQDELAYEN_WT;
      //rxMonitor.reqDelayDisable_wt        = MONITOR0_REQDELAYDIS_WT;
      //rxMonitor.reqDelayLow               = MONITOR0_REQDELAYLOW;
      //rxMonitor.reqDelayHigh              = MONITOR0_REQDELAYHIGH;
    rxMonitor.setCallbacks(rxScoreboard.monitorCbs);
     
    // Coverage class
    coverage = new();
    for (int i=0; i<FLOWS; i++)
    begin 
      string covLabel;
    
      $swrite(covLabel, "FLcoverage %0d", i);
      coverage.addFrameLinkInterface (vRX[i],covLabel);
    end  
    
    coverage.addDmaInterface (DMA,"DMAModulcoverage0");
    coverage.addDescriptorInterface (DESC,"DESCcoverage0");
    coverage.addInternalBusInterface (IB,"IBModulcoverage");
    coverage.addStatusUpManagerInterface (STAT,"SUMModulcoverage");
         
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
    for(int i=0; i<FLOWS; i++) 
      flDriver[i].setEnabled();
    descMan.setEnabled();
    dmaModul.setEnabled();
    ibModul.setEnabled();
    status.setEnabled();
    rxMonitor.setEnabled();
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
     // Disable drivers
     #(10000*CLK_PERIOD); 
     for(int i=0; i<FLOWS; i++)
       flDriver[i].setDisabled();
     // Disable monitors
     #(10000*CLK_PERIOD);
     descMan.setDisabled();
     dmaModul.setDisabled();
     ibModul.setDisabled(); 
     status.setDisabled();
     rxMonitor.setDisabled();
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
     
     enableTestEnvironment();
     
     // Run generator for one flow
     //generator.setEnabled(TRANSACTION_COUNT);

     // Run generators for more flows
     for(int i=0; i<FLOWS; i++) begin  
       generator[i].setEnabled(TRANSACTION_COUNT);
     end

     // Do nothing if the generator is enabled (for one flow)
     //while (generator.enabled)
     //  #(CLK_PERIOD);

     // Do nothing if the generators are enabled (for more flows)
     for(int i=0; i<FLOWS; i++) begin  
       while (generator[i].enabled)begin
         // stop controller 
         runtest();
         #(CLK_PERIOD);
       end  
     end 
     
     // Disable Test Enviroment
     disableTestEnvironment();

     // Display Scoreboard
     rxScoreboard.display();
     coverage.display();
     
  endtask: test1
  
  // Run test set signal RUN to different values.
  task runtest();
    // 2 flows run test
    /*#(50*CLK_PERIOD); 
    PACDMA.misc_cb.RUN <= 2'b01;
    #(100*CLK_PERIOD);
    PACDMA.misc_cb.RUN <= ~0;
    #(100*CLK_PERIOD); 
    PACDMA.misc_cb.RUN <= 2'b10;
    #(100*CLK_PERIOD);
    PACDMA.misc_cb.RUN <= ~0;
    #(100*CLK_PERIOD);
    PACDMA.misc_cb.RUN <= 2'b00;
    #(100*CLK_PERIOD);
    PACDMA.misc_cb.RUN <= ~0;
    #(100*CLK_PERIOD);*/
    
    // 4 flows run test
    #(50*CLK_PERIOD); 
    PACDMA.misc_cb.RUN <= 4'b0001;
    #(100*CLK_PERIOD);
    PACDMA.misc_cb.RUN <= ~0;
    #(100*CLK_PERIOD); 
    PACDMA.misc_cb.RUN <= 4'b0010;
    #(100*CLK_PERIOD);
    PACDMA.misc_cb.RUN <= ~0;
    #(100*CLK_PERIOD);
    PACDMA.misc_cb.RUN <= 4'b0100;
    #(100*CLK_PERIOD);
    PACDMA.misc_cb.RUN <= ~0;
    #(100*CLK_PERIOD); 
    PACDMA.misc_cb.RUN <= 4'b1000;
    #(100*CLK_PERIOD);
    PACDMA.misc_cb.RUN <= ~0;
    #(100*CLK_PERIOD);
    PACDMA.misc_cb.RUN <= 4'b0000;
    #(100*CLK_PERIOD);
    PACDMA.misc_cb.RUN <= ~0;
    #(100*CLK_PERIOD);
    
  endtask : runtest
  
  
 
  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    // -------------------------------------
    // DESIGN ENVIROMENT
    // -------------------------------------
    resetDesign();              // Reset design

    PACDMA.misc_cb.RUN <= ~0;
    #(10*CLK_PERIOD);
    createEnvironment();        // Create Test Enviroment
    
    // -------------------------------------
    // TESTING
    // -------------------------------------
    $write("\n\n############ GENERICS AND PARAMETERS ############\n\n");
    $write("------------ DUT GENERICS ---------------------\n\n");
    $write("FLOWS:\t%1d\nBUFFER_DATA_WIDTH\t%1d\nBUFFER_BLOCK_SIZE:\t%1d\nBUFFER_TOTAL_FLOW_SIZE:\t%1d\nCTRL_BUFFER_ADDR:\t%1d\nCTRL_BUFFER_GAP\t%1d\nCTRL_BUFFER_SIZE\t%1d\nCTRL_DMA_ID\t%1d\nCTRL_DMA_DATA_WIDTH:\t%1d\nCTRL_BLOCK_SIZE\t%1d\n",FLOWS,BUFFER_DATA_WIDTH,BUFFER_BLOCK_SIZE,BUFFER_TOTAL_FLOW_SIZE,CTRL_BUFFER_ADDR,CTRL_BUFFER_GAP,CTRL_BUFFER_SIZE,CTRL_DMA_ID,CTRL_DMA_DATA_WIDTH,CTRL_BLOCK_SIZE);
    $write("\n------------ RAM PARAMETERS -------------------\n\n");
    $write("RAM_SIZE:\t%1d\n",RAM_SIZE);
    $write("\n------------ TRANSACTION PARAMETERS------------\n\n");
    $write("TRANSACTION_COUNT:\t%1d\n",TRANSACTION_COUNT);

    test1();                    // Run Test 1
    
    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $stop();                    // Stop testing
  end

endprogram

