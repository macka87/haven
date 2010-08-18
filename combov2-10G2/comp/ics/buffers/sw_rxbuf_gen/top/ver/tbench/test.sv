/*
 * test.sv: SW_RX_BUFFER automatic test
 * Copyright (C) 2008 CESNET
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
 * $Id: test.sv 13962 2010-06-07 12:51:03Z xkoran01 $
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import sv_rxbuf_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
// V PRIPADE POTREBY DOPLNIT FRAMELINKOVE ROZHRANIA
program TEST (
  input  logic     CLK,
  output logic     RESET,
  iSwRxBuffer.fl_tb   FL[FLOWS],
  iSwRxBuffer.ib_tb   IB,
  iSwRxBuffer.monitor MONITOR
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
 
  // AK MA KOMPONENTA VIAC DRIVEROV ALEBO MONITOROV TREBA ICH NA TOMTO 
  // MIESTE DEKLAROVAT A V TASKU CREATEENVIRONMENT INSTANCIOVAT
  
  // Transaction
  SwRxBufferTransaction   rxBufBlueprint; 
  // Generator                            
  Generator               generator[FLOWS];
  // Driver                               
  SwRxBufferDriver #(DRIVER0_DATA_WIDTH, BLOCK_SIZE, FLOWS)  rxBufDriver[FLOWS]; 
  // Monitor      
  SwRxBufferMonitor #(MONITOR0_DATA_WIDTH, BLOCK_SIZE, FLOWS, TOTAL_FLOW_SIZE) rxBufMonitor; 
  // Responder     
  SwRxBufferResponder #(MONITOR0_DATA_WIDTH, BLOCK_SIZE, FLOWS, TOTAL_FLOW_SIZE) rxBufResponder;
  // Scoreboard  
  SwRxBufferScoreboard rxBufScoreboard; 
  // Coverage                             
  Coverage #(DRIVER0_DATA_WIDTH, MONITOR0_DATA_WIDTH, BLOCK_SIZE, FLOWS) coverage; 
  
  // Only array of virtual interfaces can be indexed 
  virtual iSwRxBuffer.fl_tb #(DRIVER0_DATA_WIDTH, BLOCK_SIZE, FLOWS) vFL[FLOWS];
  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createEnvironment();  
    // Create generator
    for(int i=0; i<FLOWS; i++) begin
      generator[i]= new("Generator", i);
      rxBufBlueprint = new;
      rxBufBlueprint.packetCount   = GENERATOR_PACKET_COUNT;
      rxBufBlueprint.packetSizeMax = GENERATOR_PACKET_SIZE_MAX;
      rxBufBlueprint.packetSizeMin = GENERATOR_PACKET_SIZE_MIN;
      assert(rxBufBlueprint.randomize());
      generator[i].blueprint = rxBufBlueprint;
    end;
        
    // Create scoreboard
    rxBufScoreboard = new;

    // Assign virtual interfaces
    vFL = FL;
    
    // Create driver    
    for(int i=0; i<FLOWS; i++) begin
      string driverLabel;
      $swrite(driverLabel, "FL Driver %d", i);

      rxBufDriver[i]    = new (driverLabel, i, generator[i].transMbx, vFL[i], rxBufScoreboard.transInfoMbx);
      rxBufDriver[i].rxDelayEn_wt             = DRIVER0_DELAYEN_WT; 
      rxBufDriver[i].rxDelayDisable_wt        = DRIVER0_DELAYDIS_WT;
      rxBufDriver[i].rxDelayLow               = DRIVER0_DELAYLOW;
      rxBufDriver[i].rxDelayHigh              = DRIVER0_DELAYHIGH;
      rxBufDriver[i].insideRxDelayEn_wt       = DRIVER0_INSIDE_DELAYEN_WT; 
      rxBufDriver[i].insideRxDelayDisable_wt  = DRIVER0_INSIDE_DELAYDIS_WT;
      rxBufDriver[i].insideRxDelayLow         = DRIVER0_INSIDE_DELAYLOW;
      rxBufDriver[i].insideRxDelayHigh        = DRIVER0_INSIDE_DELAYHIGH;
      rxBufDriver[i].setCallbacks(rxBufScoreboard.driverCbs);
    end
      
    // Create monitor
    rxBufMonitor = new ("Monitor0", MONITOR, rxBufScoreboard.transInfoMbx);
      rxBufMonitor.reqDelayEn_wt             = MONITOR0_REQDELAYEN_WT;
      rxBufMonitor.reqDelayDisable_wt        = MONITOR0_REQDELAYDIS_WT;
      rxBufMonitor.reqDelayLow               = MONITOR0_REQDELAYLOW;
      rxBufMonitor.reqDelayHigh              = MONITOR0_REQDELAYHIGH;
    // Create responder
    rxBufResponder = new ("Responder0", IB);
      rxBufResponder.txDelayEn_wt            = MONITOR0_DELAYEN_WT; 
      rxBufResponder.txDelayDisable_wt       = MONITOR0_DELAYDIS_WT;
      rxBufResponder.txDelayLow              = MONITOR0_DELAYLOW;
      rxBufResponder.txDelayHigh             = MONITOR0_DELAYHIGH;
      rxBufResponder.insideTxDelayEn_wt      = MONITOR0_INSIDE_DELAYEN_WT; 
      rxBufResponder.insideTxDelayDisable_wt = MONITOR0_INSIDE_DELAYDIS_WT;
      rxBufResponder.insideTxDelayLow        = MONITOR0_INSIDE_DELAYLOW;
      rxBufResponder.insideTxDelayHigh       = MONITOR0_INSIDE_DELAYHIGH;    
    
    // Coverage class
    // V PRIPADE VIAC INTERFACOV TREBA VOLAT PRISLUSNY 
    // COVERAGE PODLA TYPU INTERFACE
    coverage = new();
    for (int i=0; i < FLOWS; i++) begin
      string coverageLabel;
      $swrite(coverageLabel,"RXcoverage %d",i);
      coverage.addSwRxBufferInterfaceRx(vFL[i],"RXcoverage0");
    end
      coverage.addSwRxBufferInterfaceTx(MONITOR,"TXcoverage");
    // Set Callbacks
    // V PRIPADE VIAC DRIVEROV ALEBO MONITOROV TREBA VOLAT PRISLUSNE CALLBACKS
      
      rxBufMonitor.setCallbacks(rxBufScoreboard.monitorCbs);
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
    // Enable Driver, Monitor, Coverage for each port
    // V PRIPADE POTREBY ZAPNUT VSETKY POUZITE DRIVERY A MONITORY A RESPONDERY
    for(int i=0; i<FLOWS; i++) 
      rxBufDriver[i].setEnabled();
    rxBufMonitor.setEnabled();
    rxBufResponder.setEnabled();
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
     // V PRIPADE POTREBY VYPNUT VSETKY POUZITE DRIVERY A MONITORY A RESPONDERY
     // Disable drivers
     #(1000*CLK_PERIOD); 
     for(int i=0; i<FLOWS; i++)  
       rxBufDriver[i].setDisabled();
     // Disable monitors
     #(50000*CLK_PERIOD);
     rxBufMonitor.setDisabled();
     rxBufResponder.setDisabled();
     coverage.setDisabled();
  endtask : disableTestEnvironment

  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Test Case 1
  task test1();
     $write("\n\n############ TEST CASE 1 ############\n\n");
     // Enable Test environment
     enableTestEnvironment();
     // Run generators
     for(int i=0; i<FLOWS; i++) begin  
       generator[i].setEnabled(TRANSACTION_COUNT);
     end

     // Pokud je generator aktivni nic nedelej
     for(int i=0; i<FLOWS; i++) begin  
      while (generator[i].enabled)
        #(CLK_PERIOD);
    end 
     
     // Disable Test Enviroment
     disableTestEnvironment();

     // Display Scoreboard
     rxBufScoreboard.display();
     coverage.display();
  endtask: test1
  
  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    // -------------------------------------
    // DESIGN ENVIROMENT
    // -------------------------------------
    resetDesign(); // Reset design
    createEnvironment(); // Create Test Enviroment
    // -------------------------------------
    // TESTING
    // -------------------------------------
    IB.ib_cb.RD_DST_RDY <= 1;
    test1();       // Run Test 1
/*    resetDesign(); // Reset design    
    $write("TEST\n");
    
    // inicializacia
    FL[0].fl_cb.RX_DATA  <= 0;
    FL[0].fl_cb.RX_REM   <= 0;
    FL[0].fl_cb.RX_SOP_N <= 1;
    FL[0].fl_cb.RX_SOF_N <= 1;
    FL[0].fl_cb.RX_EOP_N <= 1;
    FL[0].fl_cb.RX_EOF_N <= 1;
    FL[0].fl_cb.RX_SRC_RDY_N <= 1;
    IB.ib_cb.RD_DST_RDY <= 0;
    
    @(FL[0].fl_cb);
    
    FL[0].fl_cb.RX_DATA  <= 64'h0000000000a2a1a0;
    FL[0].fl_cb.RX_REM   <= 3;
    FL[0].fl_cb.RX_SOP_N <= 0;
    FL[0].fl_cb.RX_SOF_N <= 0;
    FL[0].fl_cb.RX_EOP_N <= 0;
    FL[0].fl_cb.RX_EOF_N <= 1;
    FL[0].fl_cb.RX_SRC_RDY_N <= 0;
    IB.ib_cb.RD_DST_RDY <= 1;
    
    @(FL[0].fl_cb);
    
    FL[0].fl_cb.RX_DATA  <= 64'h0706050403020100;
    FL[0].fl_cb.RX_REM   <= 0;
    FL[0].fl_cb.RX_SOP_N <= 0;
    FL[0].fl_cb.RX_SOF_N <= 1;
    FL[0].fl_cb.RX_EOP_N <= 1;
    FL[0].fl_cb.RX_EOF_N <= 1;
        
    @(FL[0].fl_cb);
    
    FL[0].fl_cb.RX_DATA  <= 64'h0f0e0d0c0b0a0908;
    FL[0].fl_cb.RX_REM   <= 0;
    FL[0].fl_cb.RX_SOP_N <= 1;
    FL[0].fl_cb.RX_SOF_N <= 1;
    FL[0].fl_cb.RX_EOP_N <= 1;
    FL[0].fl_cb.RX_EOF_N <= 1;
        
    @(FL[0].fl_cb);
    
    FL[0].fl_cb.RX_DATA  <= 64'h1716151413121110;
    FL[0].fl_cb.RX_REM   <= 0;
    FL[0].fl_cb.RX_SOP_N <= 1;
    FL[0].fl_cb.RX_SOF_N <= 1;
    FL[0].fl_cb.RX_EOP_N <= 1;
    FL[0].fl_cb.RX_EOF_N <= 1;
    
    @(FL[0].fl_cb);
    
    FL[0].fl_cb.RX_DATA  <= 64'h1f1e1d1c1b1a1918;
    FL[0].fl_cb.RX_REM   <= 0;
    FL[0].fl_cb.RX_SOP_N <= 1;
    FL[0].fl_cb.RX_SOF_N <= 1;
    FL[0].fl_cb.RX_EOP_N <= 1;
    FL[0].fl_cb.RX_EOF_N <= 1;
    
    @(FL[0].fl_cb);
    
    FL[0].fl_cb.RX_DATA  <= 64'h2726252423222120;
    FL[0].fl_cb.RX_REM   <= 0;
    FL[0].fl_cb.RX_SOP_N <= 1;
    FL[0].fl_cb.RX_SOF_N <= 1;
    FL[0].fl_cb.RX_EOP_N <= 1;
    FL[0].fl_cb.RX_EOF_N <= 1;
    
    @(FL[0].fl_cb);
    
    FL[0].fl_cb.RX_DATA  <= 64'h2f2e2d2c2b2a2928;
    FL[0].fl_cb.RX_REM   <= 0;
    FL[0].fl_cb.RX_SOP_N <= 1;
    FL[0].fl_cb.RX_SOF_N <= 1;
    FL[0].fl_cb.RX_EOP_N <= 1;
    FL[0].fl_cb.RX_EOF_N <= 1;
    
    @(FL[0].fl_cb);
    
    FL[0].fl_cb.RX_DATA  <= 64'h0000000033323130;
    FL[0].fl_cb.RX_REM   <= 4;
    FL[0].fl_cb.RX_SOP_N <= 1;
    FL[0].fl_cb.RX_SOF_N <= 1;
    FL[0].fl_cb.RX_EOP_N <= 0;
    FL[0].fl_cb.RX_EOF_N <= 0;
    
    @(FL[0].fl_cb);
    
    FL[0].fl_cb.RX_SRC_RDY_N <= 1;
//    FL[0].fl_cb.RX_NEWLEN <= 64;
//    FL[0].fl_cb.RX_NEWLEN_DV <= 1;    
    
//    for (int i=0; i<10; i++)
      @(FL[0].fl_cb);
    
    IB.ib_cb.RD_ADDR <= 32'h00000000;
//    IB.ib_cb.RD_BE <= 1;
    IB.ib_cb.RD_REQ <= 1;
    
    @(FL[0].fl_cb);
    IB.ib_cb.RD_ADDR <= 32'h00000008;
    
    @(FL[0].fl_cb);
    IB.ib_cb.RD_ADDR <= 32'h00000010;
    
    @(FL[0].fl_cb);
    IB.ib_cb.RD_ADDR <= 32'h00000018;
    
    @(FL[0].fl_cb);
    IB.ib_cb.RD_ADDR <= 32'h00000020;
    
    @(FL[0].fl_cb);
    IB.ib_cb.RD_ADDR <= 32'h00000028;
    
    @(FL[0].fl_cb);
    IB.ib_cb.RD_ADDR <= 32'h00000030;
    
    @(FL[0].fl_cb);
    IB.ib_cb.RD_ADDR <= 32'h00000038;
    
    @(FL[0].fl_cb);
    IB.ib_cb.RD_REQ <= 0;
    
    for (int i=0; i<100; i++)
      @(FL[0].fl_cb);
*/    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $stop();       // Stop testing
  end

endprogram

