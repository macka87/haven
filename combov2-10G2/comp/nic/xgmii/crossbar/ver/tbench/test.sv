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
 * $Id: test.sv 14063 2010-06-16 12:35:47Z xsanta06 $
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import math_pkg::*;
import sv_mi32_pkg::*;
import sv_xgmii_sdr_pkg::*;
import sv_crossbar_pkg::*;
import crc32_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  output logic              RESET,
  input  logic              CLK,
  iXgmiiSdrRx.tb            XGMII_RX[XGMII_COUNT],
  iXgmiiSdrTx.tb            XGMII_TX[XGMII_COUNT],
  iMi32.tb                  MI32
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  //! XGMII Transaction
  XgmiiTransaction  xgmiiBlueprint; 
  //! XGMII Generator                            
  Generator             xgmiiGenerator[XGMII_COUNT];
  //! MI32 Generator                            
  Generator             mi32Generator;
  //! XGMII driver                               
  XgmiiSdrDriver        xgmiiDriver[XGMII_COUNT];
  //! MI32 driver                               
  Mi32Driver            mi32Driver;
  //! XGMII monitor                               
  XgmiiSdrMonitor       xgmiiMonitor[XGMII_COUNT];
  //! Scoreboard  
  XgmiiScoreboard #(XGMII_COUNT, TR_TABLE_FIRST_ONLY) crossbarScoreboard; 
  // Coverage                             
//  Coverage #(DRIVER0_DATA_WIDTH, CTRL_DMA_DATA_WIDTH, MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH) coverage; 
  
  virtual iXgmiiSdrRx.tb vXGMII_RX[XGMII_COUNT];
  virtual iXgmiiSdrTx.tb vXGMII_TX[XGMII_COUNT];

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
    // Create Generators    
    for(int i = 0; i < XGMII_COUNT; ++i) begin
        string genLabel;
        $swrite(genLabel, "XGMII Generator %0d", i);
        xgmiiGenerator[i] = new (genLabel, 0);
        
        xgmiiBlueprint = new;
        xgmiiBlueprint.dataSizeMax      = XGMII_PACKET_SIZE_MAX;
        xgmiiBlueprint.dataSizeMin      = XGMII_PACKET_SIZE_MIN;
        xgmiiBlueprint.xgmiiErrorEn_wt  = XGMII_XGMII_ERR_EN_WT;
        xgmiiBlueprint.xgmiiErrorDis_wt = XGMII_XGMII_ERR_DIS_WT;
        xgmiiBlueprint.crcErrorEn_wt    = XGMII_CRC_ERR_EN_WT;
        xgmiiBlueprint.crcErrorDis_wt   = XGMII_CRC_ERR_DIS_WT;
        xgmiiGenerator[i].blueprint = xgmiiBlueprint;
    end;

    // Create scoreboard
    crossbarScoreboard = new("Crossbar Scoreboard");   
    
    vXGMII_RX = XGMII_RX;
    vXGMII_TX = XGMII_TX;

    // Create drivers
    for(int i = 0; i < XGMII_COUNT; ++i) begin
        string driverLabel;
        $swrite(driverLabel, "XGMII Driver %0d", i);
        xgmiiDriver[i] = new (driverLabel, xgmiiGenerator[i].transMbx, vXGMII_RX[i]);
        xgmiiDriver[i].setCallbacks(crossbarScoreboard.driverCbs);
        xgmiiDriver[i].delayEn_wt          = XGMII_DELAYEN_WT; 
        xgmiiDriver[i].delayDisable_wt     = XGMII_DELAYDIS_WT;
        xgmiiDriver[i].delayLow            = XGMII_DELAYLOW;
        xgmiiDriver[i].delayHigh           = XGMII_DELAYHIGH;
    end;

    // Create monitors
    for(int i = 0; i < XGMII_COUNT; ++i) begin
        string monitorLabel;
        $swrite(monitorLabel, "XGMII Monitor %0d", i);
        xgmiiMonitor[i] = new (monitorLabel, vXGMII_TX[i]);
        xgmiiMonitor[i].setCallbacks(crossbarScoreboard.monitorCbs);
    end;
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
    for(int i = 0; i < XGMII_COUNT; ++i) begin
        xgmiiDriver[i].setEnabled();
    end;
      
    // Enable monitors
    for(int i = 0; i < XGMII_COUNT; ++i)
      xgmiiMonitor[i].setEnabled();

    // Enable coverage
   // coverage.setEnabled();
  endtask : enableTestEnvironment

  // -- Disable Test Environment ----------------------------------------------
  //! Disable Test Environment
  /*!
   * Function disables all drivers, monitors and coverages.          
   */
  task disableTestEnvironment();
    bit busy;
    int i = 0;
    #(100*CLK_PERIOD);
    // Disable drivers
    for(int i = 0; i < XGMII_COUNT; ++i) begin
        xgmiiDriver[i].setDisabled();
    end;
    
    mi32Driver.setDisabled();
      
    // Check if monitor is not receiving transaction for 100 CLK_PERIODs
    i = 0;
    while (i<100) begin
      busy = 0;
      for (int j=0; j < XGMII_COUNT; j++)
        if (xgmiiMonitor[j].busy) begin
          busy = 1;
          break;
        end

      if (busy)
        i = 0;
      else i++;
      #(CLK_PERIOD); 
    end

    // Disable monitors     
    for(int i = 0; i < XGMII_COUNT; ++i)
      xgmiiMonitor[i].setDisabled();

    // Disable coverage 
    //coverage.setDisabled();
  endtask : disableTestEnvironment

  // -- Init Crossbar --------------------------------------------------------
  //! Init Crossbar
  /*!
   * Function generates initialisation vector and sends it to DUT.          
   */
  task initCrossbar(int data, int rw);
    Mi32Transaction mi32Transaction = new();

    // Set MAC addresses
    mi32Transaction.rw      = rw;
    mi32Transaction.be      = '1;
      
    mi32Transaction.address = MI32_ADDRESS;
    mi32Transaction.data    = data;    // Set valid bit

    mi32Generator = new ("MI32 Generator", 0);

    // Create MI32 driver
    mi32Driver = new ("MI32 Driver", mi32Generator.transMbx, MI32);
    mi32Driver.txDelayEn_wt            = 0; 
    mi32Driver.txDelayDisable_wt       = 1;
    mi32Driver.txDelayLow              = 0;
    mi32Driver.txDelayHigh             = 1;

    // Enable MI32 driver
    mi32Driver.setEnabled();
    mi32Driver.sendTransaction(mi32Transaction);

    #(10*CLK_PERIOD);
  endtask : initCrossbar

  // -- Enable XGMII Generators -----------------------------------------------
  //! Enable XGMII Generators
  /*!
   * Function generates transactions and waits while generator is active 
   */
  task enableXgmiiGenerators();
    // Run XGMII Generators
    for(int i = 0; i < XGMII_COUNT; ++i) begin
        xgmiiGenerator[i].setEnabled(TRANSACTION_COUNT);
    end;

    // While XGMII Generator is active do nothing
    for(int i = 0; i < XGMII_COUNT; ++i) begin
        wait (xgmiiGenerator[i].enabled == 0);
    end;
  endtask : enableXgmiiGenerators

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
    initCrossbar(MI32_DATA_1, 1);

    // Set Scoreboard
    crossbarScoreboard.setCrossbarInterconnection(MI32_DATA_1);

    // Enable Test environment
    enableTestEnvironment();
    
    // Enable Generators and generate transactions
    enableXgmiiGenerators();

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    crossbarScoreboard.display();
//    coverage.display();
  endtask: test1

  // -- Test Case 2 -----------------------------------------------------------
  //! Test Case 2
  /*!
   * Function is responsible for running test.          
   */
  task test2();
    $write("\n\n############ TEST CASE 2 ############\n\n");
    // Init DUT
    initCrossbar(MI32_DATA_2, 1);

    // Set Scoreboard
    crossbarScoreboard.setCrossbarInterconnection(MI32_DATA_2);

    // Enable Test environment
    enableTestEnvironment();

    // Enable Generators and generate transactions
    enableXgmiiGenerators();
    
    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    crossbarScoreboard.display();
//    coverage.display();
  endtask: test2

  // -- Test Case Read --------------------------------------------------------
  //! Test Case Read
  /*!
   * Function is responsible for running test.          
   */
  task testRead();
    Mi32Transaction mi32Transaction = new();
    Mi32Monitor     mi32Monitor     = new("Mi32 Monitor", MI32);
    logic [XGMII_COUNT*log2(XGMII_COUNT)-1:0] mapping;

    mi32Transaction.address = MI32_ADDRESS;
    mi32Transaction.rw      = 0;
    mi32Transaction.be      = '1;
    mi32Monitor.executeTransaction(mi32Transaction);
    mapping = mi32Transaction.data;

    $write("\n\n############ TEST CASE READ MI32 ############\n\n");
    $write("Mapping: %b\n", mapping);
  endtask: testRead

  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    // -------------------------------------
    // DESIGN ENVIROMENT
    // -------------------------------------
    resetDesign(); // Reset design
    #(200*CLK_PERIOD);
    createEnvironment(); // Create Test Enviroment
    // -------------------------------------
    // TESTING
    // -------------------------------------
    test1();       // Run Test 1
    testRead();
    test2();       // Run Test 1
    testRead();

    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $stop();       // Stop testing
  end

endprogram

