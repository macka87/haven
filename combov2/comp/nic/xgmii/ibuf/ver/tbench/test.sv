/* \file test.sv
 * \brief IBUF Module automatic test
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
 * $Id: test.sv 14204 2010-07-02 06:58:38Z xsanta06 $
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import sv_fl_pkg::*;
import sv_mi32_pkg::*;
import sv_xgmii_sdr_driver_pkg::*;
import sv_pcd_pkg::*;
import sv_ibuf_pkg::*;
import crc32_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  output logic              RESET,
  input  logic              XGMII_CLK,
  input  logic              SAU_CLK,
  input  logic              PCD_CLK,
  input  logic              MI32_CLK,
  input  logic              FL_CLK,
  iXgmiiSdrRx.tb            XGMII,
  iSamplingUnit.tb          SAU,
  iPacodag.tb               PCD,
//  iLinkState.tb             LINK,
  iMi32.tb                  MI32,
  iFrameLinkTx.tb           FL,
  iFrameLinkTx.monitor      MONITOR
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  //! XGMII Transaction
  IbufXgmiiTransaction  xgmiiBlueprint; 
  //! MI32 Init Vector Transaction
  Mi32IbufInitVector    initVectorBlueprint; 
  //! PACODAG Transaction
  PacodagTransaction    pcdBlueprint; 
  //! XGMII Generator                            
  Generator             xgmiiGenerator;
  //! MI32 Generator                            
  Generator             mi32Generator;
  //! PACODAG Generator                            
  Generator             pcdGenerator;
  //! XGMII driver                               
  XgmiiSdrDriver        xgmiiDriver;
  //! MI32 driver                               
  Mi32Driver            mi32Driver;
  //! PACODAG driver                               
  PacodagDriver      #(PACODAG_DATA_WIDTH)   pcdDriver;
  //! Sampling Unit BFM                               
  SamplingUnit          samplingUnit;
  //! FrameLink monitor      
  FrameLinkMonitor   #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) flMonitor;
  //! FrameLink Responder     
  FrameLinkResponder #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) flResponder;
  //! Scoreboard  
  XgmiiIbufScoreboard #(TR_TABLE_FIRST_ONLY) ibufScoreboard; 
  // Coverage                             
//  Coverage #(DRIVER0_DATA_WIDTH, CTRL_DMA_DATA_WIDTH, MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) coverage; 
  
  // IBUF Config
  tIbufConfig ibufConfig;

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
    // Generate random MAC addresses
    ibufConfig.pMacs = (MAC_COUNT > MACS) ? MACS : MAC_COUNT;
    for (int i = 0; i < ibufConfig.pMacs; i++)
      for (int j = 0; j < 6; j++)
        ibufConfig.pMacAddr[i][j] = i;//$urandom();

    // Create Generators    
    xgmiiGenerator = new ("XGMII Generator", 0);
    xgmiiBlueprint = new;
    xgmiiBlueprint.dataSizeMax      = XGMII_PACKET_SIZE_MAX;
    xgmiiBlueprint.dataSizeMin      = XGMII_PACKET_SIZE_MIN;
    xgmiiBlueprint.xgmiiErrorEn_wt  = XGMII_XGMII_ERR_EN_WT;
    xgmiiBlueprint.xgmiiErrorDis_wt = XGMII_XGMII_ERR_DIS_WT;
    xgmiiBlueprint.crcErrorEn_wt    = XGMII_CRC_ERR_EN_WT;
    xgmiiBlueprint.crcErrorDis_wt   = XGMII_CRC_ERR_DIS_WT;
    xgmiiBlueprint.macCount         = ibufConfig.pMacs;
    xgmiiBlueprint.macAddr          = ibufConfig.pMacAddr;
    xgmiiGenerator.blueprint = xgmiiBlueprint;

    pcdGenerator = new ("PACODAG Generator", 0);
    pcdBlueprint = new;
    pcdBlueprint.partCount   = PACODAG_PART_COUNT;
    pcdBlueprint.partSizeMax = PACODAG_PART_SIZE_MAX;
    pcdBlueprint.partSizeMin = PACODAG_PART_SIZE_MIN;
    pcdGenerator.blueprint = pcdBlueprint;

    // Create scoreboard
    ibufScoreboard = new("IBUF Scoreboard");   
    
    xgmiiDriver = new ("XGMII Driver", xgmiiGenerator.transMbx, XGMII);
    xgmiiDriver.setCallbacks(ibufScoreboard.xgmiiDriverCbs);
      xgmiiDriver.delayEn_wt          = XGMII_DELAYEN_WT; 
      xgmiiDriver.delayDisable_wt     = XGMII_DELAYDIS_WT;
      xgmiiDriver.delayLow            = XGMII_DELAYLOW;
      xgmiiDriver.delayHigh           = XGMII_DELAYHIGH;

    // Create Sampling Unit BFM  
    samplingUnit = new ("Sampling Unit", SAU);
      samplingUnit.samplingEn_wt      = SAU_SAMPLINGEN_WT; 
      samplingUnit.samplingDis_wt     = SAU_SAMPLINGDIS_WT;
    samplingUnit.setCallbacks(ibufScoreboard.samplingCbs);
    
    // Create Pacodag Driver
    pcdDriver = new ("PACODAG Driver", pcdGenerator.transMbx, PCD);
      pcdDriver.delayEn_wt            = PACODAG_DELAYEN_WT; 
      pcdDriver.delayDisable_wt       = PACODAG_DELAYDIS_WT;
      pcdDriver.delayLow              = PACODAG_DELAYLOW;
      pcdDriver.delayHigh             = PACODAG_DELAYHIGH;
      pcdDriver.insideDelayEn_wt      = PACODAG_INSIDE_DELAYEN_WT; 
      pcdDriver.insideDelayDisable_wt = PACODAG_INSIDE_DELAYDIS_WT;
      pcdDriver.insideDelayLow        = PACODAG_INSIDE_DELAYLOW;
      pcdDriver.insideDelayHigh       = PACODAG_INSIDE_DELAYHIGH;    
    pcdDriver.setCallbacks(ibufScoreboard.pcdDriverCbs);
    
    // Create FL monitor  
    flMonitor = new ("FL Monitor", MONITOR);
    flMonitor.setCallbacks(ibufScoreboard.flMonitorCbs);
    
    // Create responder
    flResponder = new ("FL Responder", FL);
      flResponder.rxDelayEn_wt            = MONITOR0_DELAYEN_WT; 
      flResponder.rxDelayDisable_wt       = MONITOR0_DELAYDIS_WT;
      flResponder.rxDelayLow              = MONITOR0_DELAYLOW;
      flResponder.rxDelayHigh             = MONITOR0_DELAYHIGH;
      flResponder.insideRxDelayEn_wt      = MONITOR0_INSIDE_DELAYEN_WT; 
      flResponder.insideRxDelayDisable_wt = MONITOR0_INSIDE_DELAYDIS_WT;
      flResponder.insideRxDelayLow        = MONITOR0_INSIDE_DELAYLOW;
      flResponder.insideRxDelayHigh       = MONITOR0_INSIDE_DELAYHIGH;    
    
    // Coverage class
/*    coverage = new();
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
    xgmiiDriver.setEnabled();
    pcdDriver.setEnabled();
    samplingUnit.setEnabled();
      
    // Enable monitors
    flMonitor.setEnabled();
    flResponder.setEnabled();
    
    // Enable scoreboard
    ibufScoreboard.setEnabled();

    // Enable coverage
   // coverage.setEnabled();
  endtask : enableTestEnvironment

  // -- Disable Test Environment ----------------------------------------------
  //! Disable Test Environment
  /*!
   * Function disables all drivers, monitors and coverages.          
   */
  task disableTestEnvironment();
    int i = 0;

    #(1000*FL_CLK_PERIOD);
    // Disable drivers
    mi32Driver.setDisabled();
    xgmiiDriver.setDisabled();
    samplingUnit.setDisabled();
      
    // Check if monitor is not receiving transaction for 100 CLK_PERIODs
    while (i<100) begin
      if (flMonitor.busy)
        i = 0;
      else i++;
      #(FL_CLK_PERIOD); 
    end

    // Disable driver
    pcdDriver.setDisabled();

    // Disable monitors     
    flMonitor.setDisabled();
    flResponder.setDisabled();
    
    // Disable scoreboard
    ibufScoreboard.setDisabled();

    // Disable coverage 
    //coverage.setDisabled();
  endtask : disableTestEnvironment

  // -- Init IBUF -------------------------------------------------------------
  //! Init IBUF
  /*!
   * Function generates initialisation vector and sends it to DUT.          
   */
  task initIbuf();
    // Set IBUF config
    ibufConfig.pInbandfcs       = INBANDFCS;
    ibufConfig.pCtrlHdrEn       = CTRL_HDR_EN;
    ibufConfig.pCtrlFtrEn       = CTRL_FTR_EN;
    ibufConfig.pErrMaskRegXgmii = ERR_MASK_REG_XGMII;
    ibufConfig.pErrMaskRegCrc   = ERR_MASK_REG_CRC;
    ibufConfig.pErrMaskRegMintu = ERR_MASK_REG_MINTU;
    ibufConfig.pErrMaskRegMtu   = ERR_MASK_REG_MTU;
    ibufConfig.pErrMaskRegMac   = ERR_MASK_REG_MAC;
    ibufConfig.pMacCheck        = MAC_CHECK_MODE;
    ibufConfig.pMintu           = MINTU;
    ibufConfig.pMtu             = MTU;

    // Create MI32 generator
    mi32Generator = new ("MI32 Generator", 0);
    initVectorBlueprint = new(ibufConfig);
    mi32Generator.blueprint = initVectorBlueprint;

    // Create MI32 driver
    mi32Driver = new ("MI32 Driver", mi32Generator.transMbx, MI32);
    mi32Driver.txDelayEn_wt            = 0; 
    mi32Driver.txDelayDisable_wt       = 1;
    mi32Driver.txDelayLow              = 0;
    mi32Driver.txDelayHigh             = 1;

    // Set Memory of available MAC addresses
    sendMacAddr(ibufConfig);

    // Enable MI32 driver
    mi32Driver.setEnabled();

    // Run MI32 generator to initiate DUT
    mi32Generator.setEnabled(5);

    // While MI32 Generator is active do nothing
    wait (mi32Generator.enabled == 0);
    
    // Set scoreboard IBUF config
    ibufScoreboard.setIbufConfig(ibufConfig);

    #(10*FL_CLK_PERIOD);
  endtask : initIbuf

  // -- Send MAC Addresses ----------------------------------------------------
  //! Send MAC Addresses
  /*!
   * Function send MAC addresses to DUT.          
   */
  task sendMacAddr(tIbufConfig ibufConfig);
    Mi32Transaction mi32Transaction = new();

    // Set MAC addresses
    mi32Transaction.rw      = 1;
    mi32Transaction.be      = '1;

    for (int i = 0; i < ibufConfig.pMacs; i++) begin
      // Send low 32 bits
      mi32Transaction.address = 32'h80 + 8*i;

      for (int j = 0; j < 4; j++)
        for (int k = 0; k < 8; k++)
          mi32Transaction.data[j*8 + k] = ibufConfig.pMacAddr[i][j][k];

      mi32Driver.sendTransaction(mi32Transaction);

      // Send high 16 bits + valid bit
      mi32Transaction.address = 32'h84 + 8*i;
      mi32Transaction.data    = 32'h10000;    // Set valid bit

      for (int j = 0; j < 2; j++)
        for (int k = 0; k < 8; k++)
          mi32Transaction.data[j*8 + k] = ibufConfig.pMacAddr[i][j+4][k];

      mi32Driver.sendTransaction(mi32Transaction);
    end
  endtask : sendMacAddr

  // -- Read Frame Counters ---------------------------------------------------
  //! Read Frame Counters
  /*!
   * Function reads values in frame counter registers via MI32.          
   */
  task readFrameCounters();
    Mi32Transaction mi32Transaction = new();
    Mi32Monitor     mi32Monitor     = new("Mi32 Monitor", MI32);
    bit [63:0] trfc;    // Total Received Frames Counter
    bit [63:0] cfc;     // Correct Frames Counter
    bit [63:0] dfc;     // Discarded Frames Counter
    bit [63:0] bofc;    // Counter of frames discarded due to buffer overflow

    // Sample the current frame counters values
    mi32Transaction.address = 32'h2C;
    mi32Transaction.data    = 32'h1;
    mi32Transaction.rw      = 1;
    mi32Transaction.be      = '1;
    mi32Driver.sendTransaction(mi32Transaction);

    mi32Transaction.rw      = 0;
    mi32Transaction.be      = '1;
    // Read Total Received Frames Counter
     // Low part
    mi32Transaction.address = 32'h00;
    mi32Monitor.executeTransaction(mi32Transaction);
    trfc[31:0]  = mi32Transaction.data;

     // High part
    mi32Transaction.address = 32'h10;
    mi32Monitor.executeTransaction(mi32Transaction);
    trfc[63:32] = mi32Transaction.data;

    // Read Correct Frames Counter
     // Low part
    mi32Transaction.address = 32'h04;
    mi32Monitor.executeTransaction(mi32Transaction);
    cfc[31:0]  = mi32Transaction.data;

     // High part
    mi32Transaction.address = 32'h14;
    mi32Monitor.executeTransaction(mi32Transaction);
    cfc[63:32] = mi32Transaction.data;

    // Read Discarded Frames Counter
     // Low part
    mi32Transaction.address = 32'h08;
    mi32Monitor.executeTransaction(mi32Transaction);
    dfc[31:0]  = mi32Transaction.data;

     // High part
    mi32Transaction.address = 32'h18;
    mi32Monitor.executeTransaction(mi32Transaction);
    dfc[63:32] = mi32Transaction.data;

    // Read Counter of frames discarded due to buffer overflow
     // Low part
    mi32Transaction.address = 32'h0C;
    mi32Monitor.executeTransaction(mi32Transaction);
    bofc[31:0]  = mi32Transaction.data;

     // High part
    mi32Transaction.address = 32'h1C;
    mi32Monitor.executeTransaction(mi32Transaction);
    bofc[63:32] = mi32Transaction.data;

    #(20*FL_CLK_PERIOD);

    // Display counters values
    $write("------------------------------------------------------------\n");
    $write("-- IBUF Frame Counters\n");
    $write("------------------------------------------------------------\n");
    $write("Total Received Frames Counter:\t %10d\n",trfc);
    $write("Correct Frames Counter:\t\t %10d\n",cfc);
    $write("Discarded Frames Counter:\t\t %10d\n",dfc);
    $write("Discarded due to buffer overflow:\t %10d\n",bofc);
    $write("------------------------------------------------------------\n");

  endtask : readFrameCounters

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
    // Init DUT
    initIbuf();

    // Set behaviour of XGMII transaction table 
    ibufScoreboard.setTrTableBehav(XGMII_FIRST_ONLY);

    // Enable Test environment
    enableTestEnvironment();

    // Run XGMII Generator
    xgmiiGenerator.setEnabled(TRANSACTION_COUNT);

    // Run PACODAG Generator
    pcdGenerator.setEnabled(0);

    // While XGMII Generator is active do nothing
    wait (xgmiiGenerator.enabled == 0);
    
    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    ibufScoreboard.display();
//    coverage.display();
    readFrameCounters();
  endtask: test1

  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    // -------------------------------------
    // DESIGN ENVIROMENT
    // -------------------------------------
    resetDesign(); // Reset design
    #(200*FL_CLK_PERIOD);
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

