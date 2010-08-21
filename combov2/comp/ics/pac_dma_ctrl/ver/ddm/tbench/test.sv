/*
 * \file test.sv
 * \brief DDM automatic test
 * \date Copyright (C) 2009 CESNET
 * \author Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
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
 * $Id: test.sv 11320 2009-09-28 17:54:58Z xsimko03 $
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import sv_ddm_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic                  CLK,
  output logic                  RESET,
  iDdm.misc_tb                  MISC,
  iInternalBus.ib_write_tb      IB,
  iDmaCtrl.dma_tb               DMA,
  iMi32.mi32_tb                 SW,
  iDdm.rxreq_tb                 RXREQ,
  iDdm.rxnfifo_tb               RXFIFO,
  iDdm.txnfifo_tb               TXFIFO
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  
  //! DDM Transaction 
  DdmTransaction                                                 txddmBlueprint,rxddmBlueprint;
  //! Generator
  Generator                                                      txGenerator,rxGenerator;
  //! DDM Ring Modul
  DdmRingModul #(FLOWS, RING_PART_SIZE, RING_PARTS)              ring;
  //! DDM TX Driver     
  TxDdmDriver  #(FLOWS, RING_PART_SIZE, RING_PARTS)              ddmTxDriver;
  //! DDM RX Driver
  RxDdmDriver  #(FLOWS, RING_PART_SIZE, RING_PARTS)              ddmRxDriver;
  //! DDM TX Monitor 
  TxDdmMonitor #(FLOWS, BLOCK_SIZE)                              ddmTxMonitor; 
  //! DDM TX Monitor 
  RxDdmMonitor #(FLOWS, BLOCK_SIZE)                              ddmRxMonitor; 
  //! DDM RX Request Modul
  DdmRxReqModul #(FLOWS, BLOCK_SIZE, DATA_WIDTH, DMA_DATA_WIDTH,
                 DMA_ID, TRANS_TYPE, RING_PART_SIZE, RING_PARTS,
                 BLOCK_LENGTH)                                   rxreq;
  //! MI32 Modul
  DdmSoftwareModul                                               sw; 
  //! DMA Modul 
  DmaModul #(DMA_DATA_WIDTH, DMA_ID, TRANS_TYPE)                 dma;     
  //! IB Modul
  DdmIbusModul #(DATA_WIDTH, DMA_DATA_WIDTH, FLOWS,
                 DMA_ID, TRANS_TYPE, RING_PART_SIZE, RING_PARTS) ib;
  //! Scoreboard
  Scoreboard #(FLOWS, 1)                                         txScoreboard,rxScoreboard; 
  //! DDM TX Coverage
  DdmCoverage #(DATA_WIDTH, DMA_DATA_WIDTH, BLOCK_SIZE, FLOWS)   ddmCoverage;                                             
  
  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  //! Create Test Environment
  task createEnvironment();  
   
   //! Create Software Modul
   sw    = new("DDM SW Modul", SW);
   //! Create Ring Modul
   ring  = new("DDM Ring", sw);
   //! Create DMA Modul
   dma   = new("DMA modul", DMA); 
   //! Create IB Modul   
   ib    = new("DDM IB Modul", dma, ring, IB);
   //! Create RX Req Modul   
   rxreq = new("DDM RX Req Modul", ib, RXREQ);

   //! Create Generators
   txGenerator = new("TX Generator",0);
   rxGenerator = new("RX Generator",0);
   txddmBlueprint = new;
   txddmBlueprint.direction = 0;
   rxddmBlueprint = new();
   rxddmBlueprint.direction = 1;
   txGenerator.blueprint = txddmBlueprint;
   rxGenerator.blueprint = rxddmBlueprint;

   //! Create Scoreboard
   txScoreboard = new("TX");
   rxScoreboard = new("RX");

   //! Create TX Driver
   ddmTxDriver = new("DDM TX Driver", txGenerator.transMbx, ring, sw);
     ddmTxDriver.txDelayEn_wt      = TXDRIVER0_DELAYEN_WT;
     ddmTxDriver.txDelayDisable_wt = TXDRIVER0_DELAYDIS_WT;
     ddmTxDriver.txDelayLow        = TXDRIVER0_DELAYLOW;
     ddmTxDriver.txDelayHigh       = TXDRIVER0_DELAYHIGH;
     ddmTxDriver.setCallbacks(txScoreboard.driverCbs);

   //! Create RX Driver
   ddmRxDriver = new("DDM RX Driver", rxGenerator.transMbx, ring, sw);  
     ddmRxDriver.rxDelayEn_wt      = RXDRIVER0_DELAYEN_WT;
     ddmRxDriver.rxDelayDisable_wt = RXDRIVER0_DELAYDIS_WT;
     ddmRxDriver.rxDelayLow        = RXDRIVER0_DELAYLOW;
     ddmRxDriver.rxDelayHigh       = RXDRIVER0_DELAYHIGH;
     ddmRxDriver.setCallbacks(rxScoreboard.driverCbs);
   
   //! Create TX Monitor
   ddmTxMonitor = new("DDM TX Monitor", TXFIFO);
     ddmTxMonitor.setCallbacks(txScoreboard.monitorCbs);

   //! Create RX Monitor
   ddmRxMonitor = new("DDM RX Monitor", RXFIFO);
     ddmRxMonitor.setCallbacks(rxScoreboard.monitorCbs);  

   //! Create DDM Coverage
   ddmCoverage = new();
     ddmCoverage.addDmaInterface (DMA,"DDM DMA coverage");
     ddmCoverage.addInternalBusInterface (IB,"DDM IB coverage");
     ddmCoverage.addSoftwareInterface (SW,"DDM SW coverage");
     ddmCoverage.addRxReqFifoInterface (RXREQ,"DDM RXREQ coverage");
     ddmCoverage.addRxNfifoInterface (RXFIFO,"DDM RXFIFO coverage");
     ddmCoverage.addTxNfifoInterface (TXFIFO,"DDM TXFIFO coverage");
        
  endtask : createEnvironment

  // --------------------------------------------------------------------------
  //                       Test auxilarity procedures
  // --------------------------------------------------------------------------
  
  // --------------------------------------------------------------------------
  //! Resets design
  task resetDesign();
    RESET=1;                       // Init Reset variable
    #RESET_TIME     RESET = 0;     // Deactivate reset after reset_time
  endtask : resetDesign

  // --------------------------------------------------------------------------
  //! Enable test Environment
  task enableTestEnvironment();
    sw.setEnabled();
    dma.setEnabled();
    ib.setEnabled();
    ddmTxDriver.setEnabled();
    ddmRxDriver.setEnabled();
    ddmTxMonitor.setEnabled();
    ddmRxMonitor.setEnabled();
    rxreq.setEnabled();
    ddmCoverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  //! Disable test Environment
  task disableTestEnvironment();
    //! Disable drivers
    #(1000*CLK_PERIOD);
    ddmTxDriver.setDisabled();
    ddmRxDriver.setDisabled();
    //! Disable Monitor
    #(100000*CLK_PERIOD);
    sw.setDisabled();
    dma.setDisabled();
    ib.setDisabled();
    ddmTxMonitor.setDisabled();
    ddmRxMonitor.setDisabled();
    rxreq.setDisabled();
    ddmCoverage.setDisabled();
  endtask : disableTestEnvironment

  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  //! Test Case 1
  task test1();
     integer i = 0;
     tDmaRequest parsedRequest;
     $write("\n\n############ TEST CASE 1 ########################\n\n");
     //! Initialization
      #(CLK_PERIOD);
     ring.initDdm();
     ib.initIbDdm();

     //! Enable Test environment
     enableTestEnvironment();
     
     //! Run Generators
     txGenerator.setEnabled(TRANSACTION_COUNT);
     rxGenerator.setEnabled(TRANSACTION_COUNT);

     //! Do nothing while TX generator is enabled
     while (txGenerator.enabled || rxGenerator.enabled) begin
      // #(CLK_PERIOD);
       MISC.misc_cb.IDLE <=  ($rtoi($pow(2, FLOWS*2)))-1;
       ddmRxDriver.setDisabled();
       ddmTxDriver.setDisabled();
       #(1500*CLK_PERIOD);

       for(i=0; i< FLOWS; i++) begin
         //ring.pauseDdm(i,0); //! flow, direction
         ring.stopDdm(i,0); //! flow, direction
         ring.stopDdm(i,1); //! flow, direction
       end

       #(1000*CLK_PERIOD);
       
       for(i=0; i< FLOWS; i++) begin
         // Clear of HEAD register.
         ring.actDescPos[2*i+0] = RING_PART_SIZE * 16 * (2*i+0); //! 2 * flow + direction
         ddmRxDriver.rxTailPointerValue[i] = 0; //! index = flow 
         ddmRxDriver.setTailPointer(0,i);
        // ib.writeDesc(64'h00000000 + (i*2+0)*64'h1000, 0);
         ib.writeDesc(64'h0007F000 + (i*2+0)*8, 64'h2000*(i*2+0));

         ring.actDescPos[2*i+1] = RING_PART_SIZE * 16 * (2*i+1); //! 2 * flow + direction
         ddmTxDriver.txTailPointerValue[i] = 0; //! index = flow 
         ddmTxDriver.setTailPointer(0,i);
       //  ib.writeDesc(64'h00000000 + (i*2+1)*64'h1000, 0);
         ib.writeDesc(64'h0007F000 + (i*2+1)*8, 64'h2000*(i*2+1));

       end
       ddmRxDriver.setEnabled();
       ddmTxDriver.setEnabled();
       #(2000*CLK_PERIOD);

       for(i=0; i < FLOWS; i++) begin
         ring.runDdm(i,0);
         ring.runDdm(i,1);
       end
       MISC.misc_cb.IDLE <= 0;


       //! RX_RF_FULL testcase
       /*#(1000*CLK_PERIOD);
       RXREQ.rxreq_cb.RX_RF_FULL[0] <= 1;
       #(400*CLK_PERIOD);
       RXREQ.rxreq_cb.RX_RF_FULL[1] <= 1;
       #(400*CLK_PERIOD);
       RXREQ.rxreq_cb.RX_RF_FULL[2] <= 1;
       #(400*CLK_PERIOD);
       RXREQ.rxreq_cb.RX_RF_FULL[3] <= 1;
       #(1000*CLK_PERIOD);
       RXREQ.rxreq_cb.RX_RF_FULL[0] <= 0;
       #(400*CLK_PERIOD);
       RXREQ.rxreq_cb.RX_RF_FULL[1] <= 0;
       #(400*CLK_PERIOD);
       RXREQ.rxreq_cb.RX_RF_FULL[2] <= 0;
       #(400*CLK_PERIOD);
       RXREQ.rxreq_cb.RX_RF_FULL[3] <= 0;*/
     end
              
     //! Disable Test Enviroment
     disableTestEnvironment();

     //! Display Scoreboard
     txScoreboard.display();
     rxScoreboard.display();

     //! Display Coverage 
     ddmCoverage.display();
  endtask: test1

 
  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    // -------------------------------------
    // DESIGN ENVIROMENT
    // -------------------------------------
    resetDesign();              // Reset design
    createEnvironment();        // Create Test Enviroment
    
    // -------------------------------------
    // TESTING
    // -------------------------------------
    $write("\n\n############ GENERICS AND PARAMETERS ############\n\n");
    $write("------------ DUT GENERICS ---------------------\n\n");
    $write("FLOWS:\t%1d\nBASE_ADDR:B\t%1d\nBLOCK_SIZE:\t%1d\nDMA_ID:\t%1d\nDMA_DATA_WIDTH:\t%1d\nNFIFO_LUT_MEMORY\t%1d\n",FLOWS,BASE_ADDR,BLOCK_SIZE,DMA_ID,DMA_DATA_WIDTH,NFIFO_LUT_MEMORY);
    $write("\n------------ RING PARAMETERS -------------------\n\n");
    $write("RING_PART_SIZE:\t%1d\nRING_PARTS:\t%1d\n",RING_PART_SIZE,RING_PARTS);
    $write("\n------------ TRANSACTION PARAMETERS------------\n\n");
    $write("TRANSACTION_COUNT:\t%1d\n",TRANSACTION_COUNT);

    test1();                    // Run Test 1
    
    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $stop();                    // Stop testing
  end

endprogram

