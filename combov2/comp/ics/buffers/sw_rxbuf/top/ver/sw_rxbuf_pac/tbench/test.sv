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
 * $Id: test.sv 8057 2009-04-05 23:04:27Z xsanta06 $
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import sv_rxbuf_pkg::*;
import sv_rxbufpac_pkg::*;
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
  SwRxBufPacTransaction   rxBufBlueprint; 
  // Generator                            
  Generator               generator[FLOWS];
  // Driver                               
  SwRxBufPacDriver #(DRIVER0_DATA_WIDTH, BLOCK_SIZE, FLOWS)  rxBufDriver[FLOWS]; 
  // Monitor      
  SwRxBufPacMonitor #(MONITOR0_DATA_WIDTH, BLOCK_SIZE, FLOWS, TOTAL_FLOW_SIZE) rxBufMonitor; 
  // Responder     
  SwRxBufferResponder #(MONITOR0_DATA_WIDTH, BLOCK_SIZE, FLOWS, TOTAL_FLOW_SIZE) rxBufResponder;
  // Scoreboard  
  SwRxBufPacScoreboard rxBufScoreboard; 
  // Coverage                             
  Coverage #(DRIVER0_DATA_WIDTH, MONITOR0_DATA_WIDTH, BLOCK_SIZE, FLOWS) coverage; 
  
  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createEnvironment();  
    // Create generator
    if (FLOWS == 1) begin
      generator[0]= new("Generator", 0);
      rxBufBlueprint = new;
      rxBufBlueprint.packetCount   = GENERATOR_PACKET_COUNT;
      rxBufBlueprint.packetSizeMax = GENERATOR_PACKET_SIZE_MAX;
      rxBufBlueprint.packetSizeMin = GENERATOR_PACKET_SIZE_MIN;
      generator[0].blueprint = rxBufBlueprint;
    end
    else begin  
      for(int i=0; i<FLOWS; i++) begin
        generator[i]= new("Generator", i);
        rxBufBlueprint = new;
        rxBufBlueprint.packetCount   = GENERATOR_PACKET_COUNT;
        rxBufBlueprint.packetSizeMax = GENERATOR_PACKET_SIZE_MAX;
        rxBufBlueprint.packetSizeMin = GENERATOR_PACKET_SIZE_MIN;
        generator[i].blueprint = rxBufBlueprint;
      end
    end  
        
    // Create scoreboard
    rxBufScoreboard = new;
    
    // Coverage class
    coverage = new();
    
    // Create driver    
    rxBufDriver[0]    = new ("Driver0", 0, generator[0].transMbx, FL[0]);
    coverage.addSwRxBufferInterfaceRx(FL[0],"RXcoverage0");
    if (FLOWS>1) begin
      rxBufDriver[1]    = new ("Driver1", 1, generator[1].transMbx, FL[1]);
      coverage.addSwRxBufferInterfaceRx(FL[1],"RXcoverage1");
    end  
    if (FLOWS>2) begin
      rxBufDriver[2]    = new ("Driver2", 2, generator[2].transMbx, FL[2]);
      coverage.addSwRxBufferInterfaceRx(FL[2],"RXcoverage2");
      rxBufDriver[3]    = new ("Driver3", 3, generator[3].transMbx, FL[3]);
      coverage.addSwRxBufferInterfaceRx(FL[3],"RXcoverage3");
    end
    if (FLOWS>4) begin
      rxBufDriver[4]    = new ("Driver4", 4, generator[4].transMbx, FL[4]);
      coverage.addSwRxBufferInterfaceRx(FL[4],"RXcoverage4");
      rxBufDriver[5]    = new ("Driver5", 5, generator[5].transMbx, FL[5]);
      coverage.addSwRxBufferInterfaceRx(FL[5],"RXcoverage5");
      rxBufDriver[6]    = new ("Driver6", 6, generator[6].transMbx, FL[6]);
      coverage.addSwRxBufferInterfaceRx(FL[6],"RXcoverage6");
      rxBufDriver[7]    = new ("Driver7", 7, generator[7].transMbx, FL[7]);
      coverage.addSwRxBufferInterfaceRx(FL[7],"RXcoverage7");
    end  
    
    for(int i=0; i<FLOWS; i++) begin
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
    rxBufMonitor = new ("Monitor0", MONITOR);
      rxBufMonitor.reqDelayEn_wt             = MONITOR0_REQDELAYEN_WT;
      rxBufMonitor.reqDelayDisable_wt        = MONITOR0_REQDELAYDIS_WT;
      rxBufMonitor.reqDelayLow               = MONITOR0_REQDELAYLOW;
      rxBufMonitor.reqDelayHigh              = MONITOR0_REQDELAYHIGH;
    coverage.addSwRxBufferInterfaceTx(MONITOR,"TXcoverage");  
    rxBufMonitor.setCallbacks(rxBufScoreboard.monitorCbs);
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
     #(20000*CLK_PERIOD);
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
     if (FLOWS == 1) generator[0].setEnabled(TRANSACTION_COUNT);
     else
       for(int i=0; i<FLOWS; i++) begin  
         generator[i].setEnabled(TRANSACTION_COUNT);
       end

     // Pokud je generator aktivni nic nedelej
     if (FLOWS == 1) begin
       while (generator[0].enabled)
         #(CLK_PERIOD);
     end
     else     
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
    $write("\n\n############ PARAMETERS ############\n");
    $write("DATA_WIDTH:\t\t%0d\n",DATA_WIDTH);
    $write("BLOCK_SIZE:\t\t%0d\n",BLOCK_SIZE);
    $write("FLOWS:\t\t%0d\n",FLOWS);
    $write("TOTAL_FLOW_SIZE:\t%0d\n",TOTAL_FLOW_SIZE);
    
    resetDesign(); // Reset design
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

