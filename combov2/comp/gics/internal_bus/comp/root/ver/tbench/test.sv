//
// test.sv: PCIE2IB BRIDGE automatic test
// Copyright (C) 2007 CESNET
// Author(s): Tomas Malek <tomalek@liberouter.org>
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in
//    the documentation and/or other materials provided with the
//    distribution.
// 3. Neither the name of the Company nor the names of its contributors
//    may be used to endorse or promote products derived from this
//    software without specific prior written permission.
//
// This software is provided ``as is'', and any express or implied
// warranties, including, but not limited to, the implied warranties of
// merchantability and fitness for a particular purpose are disclaimed.
// In no event shall the company or contributors be liable for any
// direct, indirect, incidental, special, exemplary, or consequential
// damages (including, but not limited to, procurement of substitute
// goods or services; loss of use, data, or profits; or business
// interruption) however caused and on any theory of liability, whether
// in contract, strict liability, or tort (including negligence or
// otherwise) arising in any way out of the use of this software, even
// if advised of the possibility of such damage.
//
// $Id: test.sv 7379 2009-03-05 17:34:05Z xkobie00 $
//

import test_pkg::*;               // Test constants and types
import sv_common_pkg::*;          // System Verilog Common package
import sv_ib_pkg::*;              // System Verilog InternalBus package
import sv_pcie_pkg::*;            // System Verilog PCIe package

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input logic                 CLK,
  output logic                RESET,
  iPcieRx.driver              RX_DRIVER,
  iPcieTx.monitor             TX_MONITOR,
  iPcieTx.responder           TX_RESPONDER,
  iPcieCfg.driver             CFG_DRIVER,
  iInternalBusTx.monitor      IB_DOWN_MONITOR,
  iInternalBusTx.responder    IB_DOWN_RESPONDER,
  iInternalBusRx.driver       IB_UP_DRIVER
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  // PCIe Generator
  Generator pcieGenerator;
  // IB Generator
  Generator ibGenerator;
  // PCIe Driver
  PcieDriver pcieDriver;
  // PCIe Configuration Driver
  PcieCfgDriver cfgDriver;
  // PCIe Monitor
  PcieMonitor pcieMonitor;
  // PCIe Respnder
  PcieResponder pcieResponder;
  // PCIe Blueprint
  PcieTransaction pcieBlueprint;      
  // IB Driver
  InternalBusDriver #(pIB_DATA_WIDTH) ibDriver;
  // InternalBus Blueprint
  InternalBusTransaction ibBlueprint;
  // Internal Bus Monitor
  InternalBusMonitor #(pIB_DATA_WIDTH) ibMonitor;
  // Internal Bus Responder
  InternalBusResponder #(pIB_DATA_WIDTH) ibResponder; 
  // Internal Bus ReadResponder
  InternalBusReadResponder ibReadResponder;
  // PCIe Read Responder
  PCIeReadResponder pcieReadResponder;
  // Mailbox Binder
  MailboxBinder ibMbxBinder;
  MailboxBinder pcieMbxBinder;
  // PCIe 2 IB transformation checker
  Pcie2IbCheck pcie2ibCheck;
  // IB 2 PCIe transformation checker
  Ib2PcieCheck ib2pcieCheck;
  // PCIe posted check
  PciePostedCheck pciePostedCheck;
  // IB posted check
  IbPostedCheck ibPostedCheck;

  
  // --------------------------------------------------------------------------
  //                       Creating Enviroment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Enviroment
  task createEnviroment();
    // Create PCIe Generator
    pcieGenerator = new("PCIE Generator0", 0);
      pcieBlueprint = new;
      pcieGenerator.blueprint       = pcieBlueprint;

    // Create IB Generator
    ibGenerator = new("IB Generator0", 0);
      ibBlueprint = new;
      ibGenerator.blueprint       = ibBlueprint;

    // Mailbox Binder
    ibMbxBinder = new ("IB Mbx Binder");
    // Mailbox Binder
    pcieMbxBinder = new ("PCIE Mbx Binder");

    // Create PCIe Driver
    pcieDriver = new("PCIe Driver 0", pcieMbxBinder.transMbx, RX_DRIVER);
    // Create PCIe CFG Driver
    cfgDriver = new("PCIe CFG Driver 0", CFG_DRIVER);
    // Create IB Driver
    ibDriver = new("IB Driver 0", ibMbxBinder.transMbx, IB_UP_DRIVER);
    // Create PCIe Monitor
    pcieMonitor = new("PCIe Monitor", TX_MONITOR);
    // Create PCIe Responder
    pcieResponder = new("PCIe Responder", TX_RESPONDER);
    // Create IB Monitor
    ibMonitor = new("IB Monitor", IB_DOWN_MONITOR);
    // Create IB Responder
    ibResponder = new("IB Responder", IB_DOWN_RESPONDER);

    // Internal Bus Read Responder
    ibReadResponder = new("IB Read Responder");
    // PCIe Read Responder
    pcieReadResponder = new("PCIe Read Responder");

    // Create  PCIe 2 IB transformation checker
    pcie2ibCheck = new;
    // Create IB 2 PCIe transformation checker
    ib2pcieCheck = new;
    // Create PCIe posted check
    pciePostedCheck = new;
    // Create IB posted check
    ibPostedCheck = new;


    // Set Binder mailboxes
    ibMbxBinder.setInputMailbox(ibGenerator.transMbx);
    ibMbxBinder.setInputMailbox(ibReadResponder.transMbx);
    pcieMbxBinder.setInputMailbox(pcieGenerator.transMbx);
    pcieMbxBinder.setInputMailbox(pcieReadResponder.transMbx); 

    // Set Callbacks
    pcieDriver.setCallbacks(pcie2ibCheck.driverCbs);
    pcieDriver.setCallbacks(pciePostedCheck.driverCbs);
    pcieMonitor.setCallbacks(ib2pcieCheck.monitorCbs);
    pcieMonitor.setCallbacks(pcieReadResponder);
    pcieMonitor.setCallbacks(pciePostedCheck.monitorCbs);
    ibDriver.setCallbacks(ib2pcieCheck.driverCbs);
    ibDriver.setCallbacks(ibPostedCheck.driverCbs);
    ibMonitor.setCallbacks(pcie2ibCheck.monitorCbs);
    ibMonitor.setCallbacks(ibReadResponder);
    ibMonitor.setCallbacks(ibPostedCheck.monitorCbs);

  endtask : createEnviroment

  // --------------------------------------------------------------------------
  //                       Test auxilarity procedures
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Resets design
  task resetDesign();
    RESET=1;                       
    #cResetTime     RESET = 0;     
    @(posedge CLK);
  endtask : resetDesign

  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Test Case 1
  task totalTest();
     $write("\n\n######################### TOTAL TEST ###################################\n\n");
     
     // Set Transaction parameters for PCIe driver
     pcieBlueprint.RD32_wt = 1;
     pcieBlueprint.RD64_wt = 1;
     pcieBlueprint.WR32_wt = 1;
     pcieBlueprint.WR64_wt = 1;
     pcieBlueprint.CPLD_wt = 0;       // DO NOT SET
     pcieBlueprint.CPLD_LAST_wt = 0;  // DO NOT SET
     pcieBlueprint.maxReadRequestSize = pMAX_READ_REQUEST_SIZE;
     pcieBlueprint.maxPayloadSize     = pMAX_PAYLOAD_SIZE;
     pcieBlueprint.lengthHigh         = 10'b0000001111;
     pcieBlueprint.lengthLow          = 10'b0000000001;
     pcieGenerator.blueprint          = pcieBlueprint;

     // Set Transaction parameters for IB driver
     ibBlueprint.L2GW_wt    = 1;       // Local to Global Write
     ibBlueprint.G2LR_wt    = 1;       // Global to Local Read
     ibBlueprint.RDCL_wt    = 0;       // DO NOT SET
     ibBlueprint.lengthLow  = 12'h001;
     ibBlueprint.lengthHigh = 12'h0EF;
     ibGenerator.blueprint       = ibBlueprint;

     // Set DELAY parameters for PCIe driver
     pcieDriver.txDelayEn_wt             = 1;
     pcieDriver.txDelayDisable_wt        = 1;
     pcieDriver.insideTxDelayEn_wt       = 1; 
     pcieDriver.insideTxDelayDisable_wt  = 1;

     // Set DELAY parameters for IB driver
     ibDriver.txDelayEn_wt             = 1;
     ibDriver.txDelayDisable_wt        = 1;
     ibDriver.insideTxDelayEn_wt       = 1; 
     ibDriver.insideTxDelayDisable_wt  = 1;

     // Set DELAY parameters for IB responder
     ibResponder.rxDelayEn_wt      = 1;
     ibResponder.rxDelayDisable_wt = 1;

     // Set DELAY parameters for PCIe responder
     pcieResponder.rxDelayEn_wt      = 1;
     pcieResponder.rxDelayDisable_wt = 1;

     // Set configuration interface parameters
     cfgDriver.setMaxPayloadSize(pMAX_PAYLOAD_SIZE);
     cfgDriver.setMaxReadRequestSize(pMAX_READ_REQUEST_SIZE);
     cfgDriver.setBridgeId(pBUS_NUM, pDEVICE_NUM, pFUNC_NUM);
     ib2pcieCheck.setMaxPayloadSize(pMAX_PAYLOAD_SIZE);
     ib2pcieCheck.setMaxReadRequestSize(pMAX_READ_REQUEST_SIZE);
     ib2pcieCheck.setBridgeId(pBUS_NUM, pDEVICE_NUM, pFUNC_NUM);
     pcieReadResponder.setMaxPayloadSize(pMAX_PAYLOAD_SIZE);

     // Enable Test enviroment BMF
     pcieDriver.setEnabled();
     ibDriver.setEnabled();
     pcieMonitor.setEnabled();
     pcieResponder.setEnabled();
     ibMonitor.setEnabled();
     ibResponder.setEnabled();
     pcieReadResponder.setEnabled(); // (Disable reply completitions)
     ibReadResponder.setEnabled();
     pcieMbxBinder.setEnabled();
     ibMbxBinder.setEnabled();


     // Enable IB generator and send 1000 transactions
     ibGenerator.setEnabled(2000);
     // Enable PCIe generator and send 1000 transactions
     pcieGenerator.setEnabled(2000);

     // Wait until generation is finished
     while (ibGenerator.enabled) #(cClkPeriod);
     // Wait until generation is finished
     while (pcieGenerator.enabled) #(cClkPeriod);
    
     #(100*cClkPeriod); 

    $write("\n----------------------------------------------------\n");
    $write("\n TEST GENERATION DONE (Waiting for all transactions)\n");
    $write("\n----------------------------------------------------\n");
    #(20000*cClkPeriod); 
    pcie2ibCheck.display();
    ib2pcieCheck.display();
    pciePostedCheck.display();
    ibPostedCheck.display();
    $write("\n########################################################################\n\n\n");
  endtask: totalTest


  // --------------------------------------------------------------------------
  // RX debug testcase
  task rxDebug();
     $write("\n\n######################### RX DEBUG #################################\n\n");
     
     // Set Transaction parameters for PCIe driver
     pcieBlueprint.RD32_wt = 1;
     pcieBlueprint.RD64_wt = 1;
     pcieBlueprint.WR32_wt = 1;
     pcieBlueprint.WR64_wt = 1;
     pcieBlueprint.CPLD_wt = 0;
     pcieBlueprint.CPLD_LAST_wt = 0;
     pcieBlueprint.maxReadRequestSize = pMAX_READ_REQUEST_SIZE;
     pcieBlueprint.maxPayloadSize     = pMAX_PAYLOAD_SIZE;
     pcieBlueprint.lengthHigh         = 10'b0000001111;
     pcieBlueprint.lengthLow          = 10'b0000000000;
     pcieGenerator.blueprint          = pcieBlueprint;

     // Set DELAY parameters for PCIe driver
     pcieDriver.txDelayEn_wt             = 1;
     pcieDriver.txDelayDisable_wt        = 1;
     pcieDriver.insideTxDelayEn_wt       = 1; 
     pcieDriver.insideTxDelayDisable_wt  = 1;

     // Set DELAY parameters for IB driver
     ibDriver.txDelayEn_wt             = 1;
     ibDriver.txDelayDisable_wt        = 1;
     ibDriver.insideTxDelayEn_wt       = 1; 
     ibDriver.insideTxDelayDisable_wt  = 1;

     // Set DELAY parameters for IB responder
     ibResponder.rxDelayEn_wt      = 1;
     ibResponder.rxDelayDisable_wt = 1;

     // Set DELAY parameters for PCIe responder
     pcieResponder.rxDelayEn_wt      = 1;
     pcieResponder.rxDelayDisable_wt = 1;

     // Set configuration interface parameters
     cfgDriver.setMaxPayloadSize(pMAX_PAYLOAD_SIZE);
     cfgDriver.setMaxReadRequestSize(pMAX_READ_REQUEST_SIZE);
     cfgDriver.setBridgeId(pBUS_NUM, pDEVICE_NUM, pFUNC_NUM);
     ib2pcieCheck.setMaxPayloadSize(pMAX_PAYLOAD_SIZE);
     ib2pcieCheck.setMaxReadRequestSize(pMAX_READ_REQUEST_SIZE);
     ib2pcieCheck.setBridgeId(pBUS_NUM, pDEVICE_NUM, pFUNC_NUM);
     pcieReadResponder.setMaxPayloadSize(pMAX_PAYLOAD_SIZE);

     // Enable Test enviroment BMF
     pcieDriver.setEnabled();
     ibDriver.setEnabled();
     pcieMonitor.setEnabled();
     pcieResponder.setEnabled();
     ibMonitor.setEnabled();
     ibResponder.setEnabled();
     pcieReadResponder.setEnabled(); // (Disable reply completitions)
     ibReadResponder.setEnabled();
     pcieMbxBinder.setEnabled();
     ibMbxBinder.setEnabled();

     // Enable PCIe generator and send 10 transactions
     pcieGenerator.setEnabled(2000);

    // Wait until generation is finished
    while (pcieGenerator.enabled) #(cClkPeriod);

    $write("\n----------------------------------------------------\n");
    $write("\n TEST GENERATION DONE (Waiting for all transactions)\n");
    $write("\n----------------------------------------------------\n");
    #(10000*cClkPeriod); 
    pcie2ibCheck.display();
    ib2pcieCheck.display();
    pciePostedCheck.display();
    ibPostedCheck.display();
    $write("\n########################################################################\n\n\n");
  endtask: rxDebug

  // --------------------------------------------------------------------------
  // Test Case 1
  task txDebug();
     $write("\n\n########################### TX DEBUG ###################################\n\n");

     // Set Transaction parameters for IB driver
     ibBlueprint.L2GW_wt    = 1;       // Local to Global Write
     ibBlueprint.G2LR_wt    = 1;       // Global to Local Read
     ibBlueprint.RDCL_wt    = 0;       // Read completition (last packet)
     ibBlueprint.lengthLow  = 12'h001;
     ibBlueprint.lengthHigh = 12'h0FF;
     ibGenerator.blueprint  = ibBlueprint;

     // Set DELAY parameters for PCIe driver
     pcieDriver.txDelayEn_wt             = 1;
     pcieDriver.txDelayDisable_wt        = 1;
     pcieDriver.insideTxDelayEn_wt       = 1; 
     pcieDriver.insideTxDelayDisable_wt  = 1;

     // Set DELAY parameters for IB driver
     ibDriver.txDelayEn_wt             = 1;
     ibDriver.txDelayDisable_wt        = 1;
     ibDriver.insideTxDelayEn_wt       = 1; 
     ibDriver.insideTxDelayDisable_wt  = 1;

     // Set DELAY parameters for IB responder
     ibResponder.rxDelayEn_wt      = 1;
     ibResponder.rxDelayDisable_wt = 1;

     // Set DELAY parameters for PCIe responder
     pcieResponder.rxDelayEn_wt      = 1;
     pcieResponder.rxDelayDisable_wt = 1;

     // Set configuration interface parameters
     cfgDriver.setMaxPayloadSize(pMAX_PAYLOAD_SIZE);
     cfgDriver.setMaxReadRequestSize(pMAX_READ_REQUEST_SIZE);
     cfgDriver.setBridgeId(pBUS_NUM, pDEVICE_NUM, pFUNC_NUM);
     ib2pcieCheck.setMaxPayloadSize(pMAX_PAYLOAD_SIZE);
     ib2pcieCheck.setMaxReadRequestSize(pMAX_READ_REQUEST_SIZE);
     ib2pcieCheck.setBridgeId(pBUS_NUM, pDEVICE_NUM, pFUNC_NUM);
     pcieReadResponder.setMaxPayloadSize(pMAX_PAYLOAD_SIZE/2);

     // Enable Test enviroment BMF
     pcieDriver.setEnabled();
     ibDriver.setEnabled();
     pcieMonitor.setEnabled();
     pcieResponder.setEnabled();
     ibMonitor.setEnabled();
     ibResponder.setEnabled();
     pcieReadResponder.setEnabled();
     ibReadResponder.setEnabled();
     pcieMbxBinder.setEnabled();
     ibMbxBinder.setEnabled();

     // Enable IB generator and send 256 transactions
     ibGenerator.setEnabled(2000);
     // Wait until generation is finished
     while (ibGenerator.enabled) #(cClkPeriod);
     #(100*cClkPeriod); 

    $write("\n----------------------------------------------------\n");
    $write("\n TEST GENERATION DONE (Waiting for all transactions)\n");
    $write("\n----------------------------------------------------\n");
    #(20000*cClkPeriod); 
    pcie2ibCheck.display();
    ib2pcieCheck.display();
    pciePostedCheck.display();
    ibPostedCheck.display();
    $write("\n########################################################################\n\n\n");
  endtask: txDebug


  // --------------------------------------------------------------------------
  // Test Case 1
  task realignTest();
     $write("\n\n######################### REALIGN TEST #################################\n\n");
      // Set Transaction parameters for IB driver
     ibBlueprint.L2GW_wt    = 0;       // Local to Global Write
     ibBlueprint.G2LR_wt    = 1;       // DO NOT SET
     ibBlueprint.RDCL_wt    = 0;       // DO NOT SET
     ibBlueprint.lengthLow  = 12'h001;
     ibBlueprint.lengthHigh = 12'h0EF;
     ibGenerator.blueprint  = ibBlueprint;

     // Set DELAY parameters for PCIe driver
     pcieDriver.txDelayEn_wt             = 1;
     pcieDriver.txDelayDisable_wt        = 1;
     pcieDriver.insideTxDelayEn_wt       = 1; 
     pcieDriver.insideTxDelayDisable_wt  = 1;

     // Set DELAY parameters for IB responder
     ibResponder.rxDelayEn_wt      = 1;
     ibResponder.rxDelayDisable_wt = 1;

     // Set configuration interface parameters
     cfgDriver.setMaxPayloadSize(pMAX_PAYLOAD_SIZE);
     cfgDriver.setMaxReadRequestSize(pMAX_READ_REQUEST_SIZE);
     cfgDriver.setBridgeId(pBUS_NUM, pDEVICE_NUM, pFUNC_NUM);
     ib2pcieCheck.setMaxPayloadSize(pMAX_PAYLOAD_SIZE);
     ib2pcieCheck.setMaxReadRequestSize(pMAX_READ_REQUEST_SIZE);
     ib2pcieCheck.setBridgeId(pBUS_NUM, pDEVICE_NUM, pFUNC_NUM);
     pcieReadResponder.setMaxPayloadSize(pMAX_PAYLOAD_SIZE);

     // Enable Test enviroment BMF
     pcieDriver.setEnabled();
     ibDriver.setEnabled();
     pcieMonitor.setEnabled();
     pcieResponder.setEnabled();
     ibMonitor.setEnabled();
     ibResponder.setEnabled();
     pcieReadResponder.setEnabled(); // (Disable reply completitions)
     ibReadResponder.setEnabled();
     pcieMbxBinder.setEnabled();
     ibMbxBinder.setEnabled();


     // Enable IB generator and send 1000 transactions
     ibGenerator.setEnabled(2000);

     // Wait until generation is finished
     while (ibGenerator.enabled) #(cClkPeriod);
     #(100*cClkPeriod); 

    $write("\n----------------------------------------------------\n");
    $write("\n TEST GENERATION DONE (Waiting for all transactions)\n");
    $write("\n----------------------------------------------------\n");
    #(20000*cClkPeriod); 
    pcie2ibCheck.display();
    ib2pcieCheck.display();
    pciePostedCheck.display();
    ibPostedCheck.display();
    $write("\n########################################################################\n\n\n");
  endtask: realignTest


  // --------------------------------------------------------------------------
  // Test Case 1
  task writeSplitTest();
     $write("\n\n######################### WRITE SPLIT TEST #############################\n\n");
     
     // Set Transaction parameters for PCIe driver
     pcieBlueprint.RD32_wt = 0;
     pcieBlueprint.RD64_wt = 0;
     pcieBlueprint.WR32_wt = 1;
     pcieBlueprint.WR64_wt = 1;
     pcieBlueprint.CPLD_wt = 0;       // DO NOT SET
     pcieBlueprint.CPLD_LAST_wt = 0;  // DO NOT SET
//     pcieBlueprint.maxReadRequestSize = pMAX_READ_REQUEST_SIZE;
//     pcieBlueprint.maxPayloadSize     = pMAX_PAYLOAD_SIZE;
     pcieBlueprint.lengthHigh         = 10'b0000001111;
     pcieBlueprint.lengthLow          = 10'b0000000001;
     pcieGenerator.blueprint          = pcieBlueprint;

     // Set Transaction parameters for IB driver
     ibBlueprint.L2GW_wt        = 1;       // Local to Global Write
     ibBlueprint.G2LR_wt        = 0;       // Global to Local Read
     ibBlueprint.RDCL_wt        = 0;       // SET and disable (PCIE_POST_CHECK)
     ibBlueprint.lengthLow      = 12'h080;
     ibBlueprint.lengthHigh     = 12'h1FF;
     ibBlueprint.globalAddrLow  = 64'h000000000000000;
     ibBlueprint.globalAddrHigh = 64'h0000001FFFFFFFF;

// RD/WR 0 test (FIX BUGS)
//   ibBlueprint.lengthLow      = 12'h000;
//   ibBlueprint.lengthHigh     = 12'h000;
//   ibBlueprint.globalAddrLow  = 64'h000000000000000;
//   ibBlueprint.globalAddrHigh = 64'h000000000000000;
//   ibBlueprint.localAddrLow   = 32'h00000000;
//   ibBlueprint.localAddrHigh  = 32'h00000000;
   ibGenerator.blueprint      = ibBlueprint;

     // Set DELAY parameters for PCIe driver
     pcieDriver.txDelayEn_wt             = 0;
     pcieDriver.txDelayDisable_wt        = 1;
     pcieDriver.insideTxDelayEn_wt       = 0; 
     pcieDriver.insideTxDelayDisable_wt  = 1;

     // Set DELAY parameters for IB driver
     ibDriver.txDelayEn_wt             = 1;
     ibDriver.txDelayDisable_wt        = 1;
     ibDriver.insideTxDelayEn_wt       = 1; 
     ibDriver.insideTxDelayDisable_wt  = 1;

     // Set DELAY parameters for IB responder
     ibResponder.rxDelayEn_wt      = 0;
     ibResponder.rxDelayDisable_wt = 1;

     // Set DELAY parameters for PCIe responder
     pcieResponder.rxDelayEn_wt      = 1;
     pcieResponder.rxDelayDisable_wt = 1;

     // Set configuration interface parameters
     cfgDriver.setMaxPayloadSize(128);//pMAX_PAYLOAD_SIZE);
     cfgDriver.setMaxReadRequestSize(128);//pMAX_READ_REQUEST_SIZE);
     cfgDriver.setBridgeId(pBUS_NUM, pDEVICE_NUM, pFUNC_NUM);
     ib2pcieCheck.setMaxPayloadSize(128);//pMAX_PAYLOAD_SIZE);
     ib2pcieCheck.setMaxReadRequestSize(128);//pMAX_READ_REQUEST_SIZE);
     ib2pcieCheck.setBridgeId(pBUS_NUM, pDEVICE_NUM, pFUNC_NUM);
     pcieReadResponder.setMaxPayloadSize(128);//pMAX_PAYLOAD_SIZE);

     // Enable Test enviroment BMF
     pcieDriver.setEnabled();
     ibDriver.setEnabled();
     pcieMonitor.setEnabled();
     pcieResponder.setEnabled();
     ibMonitor.setEnabled();
     ibResponder.setEnabled();
     pcieReadResponder.setEnabled(); // (Disable reply completitions)
     ibReadResponder.setEnabled();
     pcieMbxBinder.setEnabled();
     ibMbxBinder.setEnabled();

     // Enable IB generator and send 1000 transactions
     ibGenerator.setEnabled(2000);

     // Wait until generation is finished
     while (ibGenerator.enabled) #(cClkPeriod);
    
     #(100*cClkPeriod); 

    $write("\n----------------------------------------------------\n");
    $write("\n TEST GENERATION DONE (Waiting for all transactions)\n");
    $write("\n----------------------------------------------------\n");
    #(20000*cClkPeriod); 
    pcie2ibCheck.display();
    ib2pcieCheck.display();
    pciePostedCheck.display();
    ibPostedCheck.display();
    $write("\n########################################################################\n\n\n");
  endtask: writeSplitTest



    // --------------------------------------------------------------------------
  // Test Case 1
  task readSplitTest();
     $write("\n\n######################## READ SPLIT TEST ###############################\n\n");
     
     // Set Transaction parameters for PCIe driver
     pcieBlueprint.RD32_wt = 1;
     pcieBlueprint.RD64_wt = 1;
     pcieBlueprint.WR32_wt = 1;
     pcieBlueprint.WR64_wt = 1;
     pcieBlueprint.CPLD_wt = 0;       // DO NOT SET
     pcieBlueprint.CPLD_LAST_wt = 0;  // DO NOT SET
//   pcieBlueprint.maxReadRequestSize = pMAX_READ_REQUEST_SIZE;
//   pcieBlueprint.maxPayloadSize     = pMAX_PAYLOAD_SIZE;
     pcieBlueprint.lengthHigh         = 10'b0000001111;
     pcieBlueprint.lengthLow          = 10'b0000000001;
     pcieGenerator.blueprint          = pcieBlueprint;

     // Set Transaction parameters for IB driver
     ibBlueprint.L2GW_wt    = 0;       // Local to Global Write
     ibBlueprint.G2LR_wt    = 1;       // Global to Local Read
     ibBlueprint.RDCL_wt    = 0;       // DO NOT SET
     ibBlueprint.lengthLow  = 12'h080;
     ibBlueprint.lengthHigh = 12'h1FF;
     ibGenerator.blueprint  = ibBlueprint;

     // Set DELAY parameters for PCIe driver
     pcieDriver.txDelayEn_wt             = 1;
     pcieDriver.txDelayDisable_wt        = 1;
     pcieDriver.insideTxDelayEn_wt       = 1; 
     pcieDriver.insideTxDelayDisable_wt  = 1;

     // Set DELAY parameters for IB driver
     ibDriver.txDelayEn_wt             = 1;
     ibDriver.txDelayDisable_wt        = 1;
     ibDriver.insideTxDelayEn_wt       = 1; 
     ibDriver.insideTxDelayDisable_wt  = 1;

     // Set DELAY parameters for IB responder
     ibResponder.rxDelayEn_wt      = 1;
     ibResponder.rxDelayDisable_wt = 1;

     // Set DELAY parameters for PCIe responder
     pcieResponder.rxDelayEn_wt      = 1;
     pcieResponder.rxDelayDisable_wt = 1;

     // Set configuration interface parameters
     cfgDriver.setMaxPayloadSize(128);//pMAX_PAYLOAD_SIZE);
     cfgDriver.setMaxReadRequestSize(256);//pMAX_READ_REQUEST_SIZE);
     cfgDriver.setBridgeId(pBUS_NUM, pDEVICE_NUM, pFUNC_NUM);
     ib2pcieCheck.setMaxPayloadSize(128);//pMAX_PAYLOAD_SIZE);
     ib2pcieCheck.setMaxReadRequestSize(256);//pMAX_READ_REQUEST_SIZE);
     ib2pcieCheck.setBridgeId(pBUS_NUM, pDEVICE_NUM, pFUNC_NUM);
     pcieReadResponder.setMaxPayloadSize(128);//pMAX_PAYLOAD_SIZE);

     // Enable Test enviroment BMF
     pcieDriver.setEnabled();
     ibDriver.setEnabled();
     pcieMonitor.setEnabled();
     pcieResponder.setEnabled();
     ibMonitor.setEnabled();
     ibResponder.setEnabled();
     pcieReadResponder.setEnabled(); // (Disable reply completitions)
     ibReadResponder.setEnabled();
     pcieMbxBinder.setEnabled();
     ibMbxBinder.setEnabled();

     // Enable IB generator and send 1000 transactions
     ibGenerator.setEnabled(1000);

     // Wait until generation is finished
     while (ibGenerator.enabled) #(cClkPeriod);
    
     #(100*cClkPeriod); 

    $write("\n----------------------------------------------------\n");
    $write("\n TEST GENERATION DONE (Waiting for all transactions)\n");
    $write("\n----------------------------------------------------\n");
    #(20000*cClkPeriod); 
    pcie2ibCheck.display();
    ib2pcieCheck.display();
    pciePostedCheck.display();
    ibPostedCheck.display();
    $write("\n########################################################################\n\n\n");
  endtask: readSplitTest



  // --------------------------------------------------------------------------
  // Test Case 1
  task resetTest();
     $write("\n\n######################### RESET TEST ###################################\n\n");
     
     // Set Transaction parameters for PCIe driver
     pcieBlueprint.RD32_wt = 1;
     pcieBlueprint.RD64_wt = 1;
     pcieBlueprint.WR32_wt = 1;
     pcieBlueprint.WR64_wt = 1;
     pcieBlueprint.CPLD_wt = 0;       // DO NOT SET
     pcieBlueprint.CPLD_LAST_wt = 0;  // DO NOT SET
     pcieBlueprint.maxReadRequestSize = pMAX_READ_REQUEST_SIZE;
     pcieBlueprint.maxPayloadSize     = pMAX_PAYLOAD_SIZE;
     pcieBlueprint.lengthHigh         = 10'b0000001111;
     pcieBlueprint.lengthLow          = 10'b0000000001;
     pcieGenerator.blueprint          = pcieBlueprint;

     // Set Transaction parameters for IB driver
     ibBlueprint.L2GW_wt    = 1;       // Local to Global Write
     ibBlueprint.G2LR_wt    = 1;       // Global to Local Read
     ibBlueprint.RDCL_wt    = 0;       // DO NOT SET
     ibBlueprint.lengthLow  = 12'h001;
     ibBlueprint.lengthHigh = 12'h0EF;
     ibGenerator.blueprint       = ibBlueprint;

     // Set DELAY parameters for PCIe driver
     pcieDriver.txDelayEn_wt             = 1;
     pcieDriver.txDelayDisable_wt        = 1;
     pcieDriver.insideTxDelayEn_wt       = 1; 
     pcieDriver.insideTxDelayDisable_wt  = 1;

     // Set DELAY parameters for IB driver
     ibDriver.txDelayEn_wt             = 1;
     ibDriver.txDelayDisable_wt        = 1;
     ibDriver.insideTxDelayEn_wt       = 1; 
     ibDriver.insideTxDelayDisable_wt  = 1;

     // Set DELAY parameters for IB responder
     ibResponder.rxDelayEn_wt      = 1;
     ibResponder.rxDelayDisable_wt = 1;

     // Set DELAY parameters for PCIe responder
     pcieResponder.rxDelayEn_wt      = 1;
     pcieResponder.rxDelayDisable_wt = 1;

     // Set configuration interface parameters
     cfgDriver.setMaxPayloadSize(pMAX_PAYLOAD_SIZE);
     cfgDriver.setMaxReadRequestSize(pMAX_READ_REQUEST_SIZE);
     cfgDriver.setBridgeId(pBUS_NUM, pDEVICE_NUM, pFUNC_NUM);
     ib2pcieCheck.setMaxPayloadSize(pMAX_PAYLOAD_SIZE);
     ib2pcieCheck.setMaxReadRequestSize(pMAX_READ_REQUEST_SIZE);
     ib2pcieCheck.setBridgeId(pBUS_NUM, pDEVICE_NUM, pFUNC_NUM);
     pcieReadResponder.setMaxPayloadSize(pMAX_PAYLOAD_SIZE);

     // Enable Test enviroment BMF
     pcieDriver.setEnabled();
     ibDriver.setEnabled();
     pcieMonitor.setEnabled();
     pcieResponder.setEnabled();
     ibMonitor.setEnabled();
     ibResponder.setEnabled();
     pcieReadResponder.setEnabled(); // (Disable reply completitions)
     ibReadResponder.setEnabled();
     pcieMbxBinder.setEnabled();
     ibMbxBinder.setEnabled();


     // Enable IB generator and send 1000 transactions
     ibGenerator.setEnabled(100);
     // Enable PCIe generator and send 1000 transactions
     pcieGenerator.setEnabled(100);

     // Wait until generation is finished
     while (ibGenerator.enabled) #(cClkPeriod);
     // Wait until generation is finished
     while (pcieGenerator.enabled) #(cClkPeriod);
     #(2000*cClkPeriod); 

     resetDesign();      // Reset design

     // Enable IB generator and send 1000 transactions
     ibGenerator.setEnabled(100);
     // Enable PCIe generator and send 1000 transactions
     pcieGenerator.setEnabled(100);

     // Wait until generation is finished
     while (ibGenerator.enabled) #(cClkPeriod);
     // Wait until generation is finished
     while (pcieGenerator.enabled) #(cClkPeriod);
     #(2000*cClkPeriod);

     resetDesign();      // Reset design

     // Enable IB generator and send 1000 transactions
     ibGenerator.setEnabled(100);
     // Enable PCIe generator and send 1000 transactions
     pcieGenerator.setEnabled(100);

     // Wait until generation is finished
     while (ibGenerator.enabled) #(cClkPeriod);
     // Wait until generation is finished
     while (pcieGenerator.enabled) #(cClkPeriod);
     #(2000*cClkPeriod); 

    $write("\n----------------------------------------------------\n");
    $write("\n TEST GENERATION DONE (Waiting for all transactions)\n");
    $write("\n----------------------------------------------------\n");
    #(2000*cClkPeriod); 
    pcie2ibCheck.display();
    ib2pcieCheck.display();
    pciePostedCheck.display();
    ibPostedCheck.display();
    $write("\n########################################################################\n\n\n");
  endtask: resetTest



  // --------------------------------------------------------------------------
  // Test Case 1
  task error_test();
     $write("\n\n######################### ERROR TEST #################################\n\n");
      // Set Transaction parameters for IB driver
     ibBlueprint.L2GW_wt    = 1;       // Local to Global Write
     ibBlueprint.G2LR_wt    = 0;       // DO NOT SET
     ibBlueprint.RDCL_wt    = 0;       // DO NOT SET
     ibBlueprint.lengthLow  = 12'h000;
     ibBlueprint.lengthHigh = 12'h000;
     ibBlueprint.globalAddrLow  = 64'h0000000358A0000;
     ibBlueprint.globalAddrHigh = 64'h0000000358A0000;
     ibBlueprint.localAddrLow   = 32'h00001000;
     ibBlueprint.localAddrHigh  = 32'h00001000;
     ibGenerator.blueprint  = ibBlueprint;

     // Set DELAY parameters for PCIe driver
     pcieDriver.txDelayEn_wt             = 1;
     pcieDriver.txDelayDisable_wt        = 1;
     pcieDriver.insideTxDelayEn_wt       = 1; 
     pcieDriver.insideTxDelayDisable_wt  = 1;

     // Set DELAY parameters for IB responder
     ibResponder.rxDelayEn_wt      = 0;
     ibResponder.rxDelayDisable_wt = 1;

     // Set DELAY parameters for PCIe responder
     pcieResponder.rxDelayEn_wt      = 0;
     pcieResponder.rxDelayDisable_wt = 1;

     // Set DELAY parameters for IB driver
     ibDriver.txDelayEn_wt             = 0;
     ibDriver.txDelayDisable_wt        = 1;
     ibDriver.insideTxDelayEn_wt       = 0; 
     ibDriver.insideTxDelayDisable_wt  = 1;


     // Set configuration interface parameters
     cfgDriver.setMaxPayloadSize(pMAX_PAYLOAD_SIZE);
     cfgDriver.setMaxReadRequestSize(pMAX_READ_REQUEST_SIZE);
     cfgDriver.setBridgeId(pBUS_NUM, pDEVICE_NUM, pFUNC_NUM);
     ib2pcieCheck.setMaxPayloadSize(pMAX_PAYLOAD_SIZE);
     ib2pcieCheck.setMaxReadRequestSize(pMAX_READ_REQUEST_SIZE);
     ib2pcieCheck.setBridgeId(pBUS_NUM, pDEVICE_NUM, pFUNC_NUM);
     pcieReadResponder.setMaxPayloadSize(pMAX_PAYLOAD_SIZE);

     // Enable Test enviroment BMF
     pcieDriver.setEnabled();
     ibDriver.setEnabled();
     pcieMonitor.setEnabled();
     pcieResponder.setEnabled();
     ibMonitor.setEnabled();
     ibResponder.setEnabled();
     pcieReadResponder.setEnabled(); // (Disable reply completitions)
     ibReadResponder.setEnabled();
     pcieMbxBinder.setEnabled();
     ibMbxBinder.setEnabled();


     // Enable IB generator and send 1000 transactions
     ibGenerator.setEnabled(10);

     // Wait until generation is finished
     while (ibGenerator.enabled) #(cClkPeriod);
     #(100*cClkPeriod); 

    $write("\n----------------------------------------------------\n");
    $write("\n TEST GENERATION DONE (Waiting for all transactions)\n");
    $write("\n----------------------------------------------------\n");
    #(20000*cClkPeriod); 
    pcie2ibCheck.display();
    ib2pcieCheck.display();
    pciePostedCheck.display();
    ibPostedCheck.display();
    $write("\n########################################################################\n\n\n");
  endtask: error_test


  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    // -------------------------------------
     // DESIGN ENVIROMENT
     // -------------------------------------
     createEnviroment(); // Create Test Enviroment
     // -------------------------------------
     // TESTING
     // -------------------------------------
     resetDesign();      // Reset design
    

     //error_test();
     //realignTest();
     totalTest();       // NOTE: PASSED
     // rxDebug();         // NOTE: PASSED
     // txDebug();         // NOTE: PASSED
     // writeSplitTest();  // NOTE: PASSED
     // readSplitTest();   // NOTE: PASSED
     // resetTest();       // NOTE: PASSED
     // -------------------------------------
     // STOP TESTING
     // -------------------------------------
     $stop();       // Stop testing
  end

endprogram : TEST



