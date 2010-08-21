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
// $Id: test.sv 2981 2008-06-30 09:16:01Z tomalek $
//

import test_pkg::*;             // Test constants and types

import ib_transaction_pkg::*;   // Internal Bus Transaction class
import ib_driver_pkg::*;        // Internal Bus Driver class
import ib_generator_pkg::*;     // Internal Bus Generator
import ib_monitor_pkg::*;       // Internal Bus Monitor

import pcie_transaction_pkg::*; // PCIe Transaction class
import pcie_driver_pkg::*;      // PCIe Driver class
import pcie_generator_pkg::*;   // PCIe Generator
import pcie_monitor_pkg::*;     // PCIe Monitor

import bm_transaction_pkg::*;   // BM Transaction class
import bm_driver_pkg::*;        // BM Driver class
import bm_generator_pkg::*;     // BM Generator
import bm_monitor_pkg::*;       // BM Monitor

import scoreboard_pkg::*;      // Scoreboard Package

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST(
  input logic                 CLK,
  output logic                RESET,
  iPcieRx.bridge              RX,
  iPcieTx.bridge              TX,  
  iPcieCfg.bridge             CFG,
  iIbBm64.comp                BM,
  iInternalBusLink.tx         IB_DOWN,
  iInternalBusLink.rx         IB_UP
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  InternalBusDriver    ibDriver;              // Internal Bus Driver
  InternalBusGenerator ibGenerator;           // Internal Bus Generator
  InternalBusMonitor   ibMonitor;             // Internal Bus Monitor

  PcieDriver           pcieDriver;            // PCIe Driver
  PcieGenerator        pcieGenerator;         // PCIe Generator
  PcieMonitor          pcieMonitor;           // PCIe Monitor  

  BusMasterDriver      bmDriver;              // Bus Master Driver
  BusMasterGenerator   bmGenerator;           // Bus Master Generator
  BusMasterMonitor     bmMonitor;             // Bus Master Monitor  

  Scoreboard           scoreboard;            // Scoreboard

  tIbTransMbx          ibTransMbx   = new(1); // IB Transaction MailBox  
  tBmTransMbx          bmTransMbx   = new(1); // BM Transaction MailBox
  tPcieTransMbx        pcieTransMbx = new(1); // PCIE Transaction MailBox
  
  // --------------------------------------------------------------------------
  //                       Creating Enviroment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Enviroment
  task createEnviroment();

     // Create BFM objects
     ibDriver       = new(ibTransMbx, IB_UP, 0);   
     ibMonitor      = new(IB_DOWN, 0);             
     ibGenerator    = new(ibTransMbx);             
     pcieGenerator  = new(pcieTransMbx);
     pcieDriver     = new(pcieTransMbx, RX, CFG, 0);
     pcieMonitor    = new(TX, 0);            
     bmDriver       = new(bmTransMbx, BM);  
     bmMonitor      = new(BM);
     bmGenerator    = new(bmTransMbx);      
     
     scoreboard     = new(CFG); 
     
     // Set Callbacks
     ibMonitor.setCallbacks(scoreboard.ibMonitorCbs);
     pcieMonitor.setCallbacks(scoreboard.pcieMonitorCbs);    
     bmMonitor.setCallbacks(scoreboard.bmMonitorCbs);     
     ibDriver.setCallbacks(scoreboard.ibDriverCbs);
     pcieDriver.setCallbacks(scoreboard.pcieDriverCbs);     
     bmDriver.setCallbacks(scoreboard.bmDriverCbs);      

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

  //-------------------------------------------------------------------------- 
  // Create own hand-made IB transaction for sending 
  function InternalBusTransaction handMadeIbTr();
    InternalBusTransaction ibTr = new();        

    ibTr.localAddr    = 32'h00008b08;  
    ibTr.globalAddr   = 64'h100000000a459ba5; //64'h00bbc4410a459ba5; //1  
    ibTr.tag          = 9;     
    ibTr.length       = 12'h185;
    ibTr.transType    = L2GW;  
    ibTr.data         = new[ibTr.length];      
    
    for (integer i=0; i < ibTr.data.size; i++) ibTr.data[i] = i+1; 

    handMadeIbTr = ibTr;      
  endfunction : handMadeIbTr

  //-------------------------------------------------------------------------- 
  // Create own hand-made IB transaction for sending 
  function InternalBusTransaction handMadeIbTr2();
    InternalBusTransaction ibTr = new();        

    ibTr.localAddr    = 32'h00002201;  
    ibTr.globalAddr   = 32'hA1D6FD01;  
    ibTr.tag          = 2;     
    ibTr.length       = 12'h00F;;
    ibTr.transType    = G2LR;  
    ibTr.data         = new[ibTr.length];                          
    
    //for (integer i=0; i < ibTr.data.size; i++) ibTr.data[i] = i; 
    
    handMadeIbTr2 = ibTr;      
  endfunction : handMadeIbTr2  

  //-------------------------------------------------------------------------- 
  // Create own hand-made PCIE transaction for sending 
  function PcieTransaction handMadePcieTr();
    PcieTransaction pcieTr = new();        

    pcieTr.address      = {32'h00000000,32'h0000A000};      
    pcieTr.transType    = (pcieTr.address[63:32] == 32'h00000000) ? WR32 : WR64; 
    pcieTr.length       = 10'b0000000011;;
    pcieTr.lastBE       = L1111;
    pcieTr.firstBE      = F1111;
    pcieTr.tag          = 3; 
    pcieTr.tc           = 0;      
    pcieTr.td           = 0;         
    pcieTr.ep           = 0;
    pcieTr.attr         = 0;  
    pcieTr.barHitN      = B1111110;
    pcieTr.supported    = 1;
    pcieTr.busnum_req   = CFG.BUS_NUM;
    pcieTr.devnum_req   = CFG.DEVICE_NUM;
    pcieTr.funcnum_req  = CFG.FUNC_NUM;     
    pcieTr.data         = new[12];   

    for (integer i=0; i < pcieTr.data.size; i++) pcieTr.data[i] = i;    
    
    handMadePcieTr = pcieTr;      
  endfunction : handMadePcieTr    

  //-------------------------------------------------------------------------- 
  // Create own hand-made PCIE transaction for sending 
  function PcieTransaction handMadePcieTr2();
    PcieTransaction pcieTr = new();        

    pcieTr.address      = {32'h00000000,32'h0000A000};    
    pcieTr.transType    = (pcieTr.address[63:32] == 32'h00000000) ? RD32 : RD64; 
    pcieTr.length       = 10'b0000000011;
    pcieTr.lastBE       = L1111;
    pcieTr.firstBE      = F1111;
    pcieTr.tag          = 3; 
    pcieTr.tc           = 0;      
    pcieTr.td           = 0;         
    pcieTr.ep           = 0;
    pcieTr.attr         = 0;  
    pcieTr.barHitN      = B1111110;
    pcieTr.supported    = 1;
    pcieTr.busnum_req   = CFG.BUS_NUM;
    pcieTr.devnum_req   = CFG.DEVICE_NUM;
    pcieTr.funcnum_req  = CFG.FUNC_NUM;     
    //pcieTr.data         = new[pcieTr.getLengthInB()];   

    //for (integer i=0; i < pcieTr.data.size; i++) pcieTr.data[i] = i;    
    
    handMadePcieTr2 = pcieTr;      
  endfunction : handMadePcieTr2     

  //-------------------------------------------------------------------------- 
  // Create own hand-made BM transaction for sending 
  function BusMasterTransaction handMadeBmTr();
    BusMasterTransaction bmTr = new();        

    bmTr.localAddr    = 32'h00002201;  
    bmTr.globalAddr   = 32'hA1D6FD01;  
    bmTr.tag          = 2;     
    bmTr.length       = 12'h00F;;
    bmTr.transType    = BM_G2LR;  
    
    handMadeBmTr = bmTr;      
  endfunction : handMadeBmTr    

  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Test Case 1
  task test1();
     $write("\n\n########################### TEST CASE 1 ################################\n\n");

     // Enable Test enviroment BFM/objects
     ibMonitor.setEnabled();
     pcieMonitor.setEnabled();
     bmMonitor.setEnabled();     
     ibDriver.setEnabled();
     pcieDriver.setEnabled();
     bmDriver.setEnabled();
     
     // Run generators or send hand-made transaction
     ibGenerator.setEnabled();   //ibDriver.sendTransaction(handMadeIbTr());
     pcieGenerator.setEnabled(); //pcieDriver.sendTransaction(handMadePcieTr());       
     bmGenerator.setEnabled();   //bmDriver.sendTransaction(handMadeBmTr());
               
     // START // **************************************************************
     
     // Enable/disable master/slave/bm transaction
     //scoreboard.enableMasterTransactions();
     scoreboard.enableSlaveTransactions();  
     //scoreboard.enableBmTransactions();                         

     // Run test for many clock cycles
     #(10*cClkPeriod); 

     // Disable master+slave+bm transactions
     scoreboard.disableMasterTransactions();
     scoreboard.disableSlaveTransactions();
     scoreboard.disableBmTransactions();               

     // Wait for finishing transactions and disable monitors
     #(1000*cClkPeriod);

     // FINISH // *************************************************************

     // Display scoreboard tables
     scoreboard.ibTransactionTable.display(1);
     scoreboard.pcieTransactionTable.display(1);
     //scoreboard.bmTransactionTable.display();     

     $write("\n########################################################################\n\n\n");
  endtask: test1

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
     resetDesign(); // Reset design
     test1();       // Run Test 1

     // -------------------------------------
     // STOP TESTING
     // -------------------------------------

     $stop();       // Stop testing
  end

endprogram : TEST



