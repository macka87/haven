/*
 * test.sv: IB_SWITCH automatic test
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobiersky <kobiersky@liberouter.org>
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
 * $Id: test.sv 14975 2010-08-11 09:27:06Z xjanal01 $
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import sv_fl_pkg::*;
import test_pkg::*;
import sv_mi32_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
// V PRIPADE POTREBY DOPLNIT FRAMELINKOVE ROZHRANIA
program TEST (
  input  logic     CLK,
  output logic     RESET,
  iFrameLinkRx.tb  RX,
  iFrameLinkTx.tb  TX,
  iFrameLinkTx.monitor MONITOR,
  iMi32.tb         MI32_RXTX
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
 
  // AK MA KOMPONENTA VIAC DRIVEROV ALEBO MONITOROV TREBA ICH NA TOMTO 
  // MIESTE DEKLAROVAT A V TASKU CREATEENVIRONMENT INSTANCIOVAT
  
  // Transaction
  FrameLinkTransaction    flBlueprint; 
  // Generator                            
  Generator               generator;
  // Driver                               
  FrameLinkDriver #(DRIVER0_DATA_WIDTH, DRIVER0_DREM_WIDTH)       flDriver; 
  // Monitor      
  FrameLinkMonitor #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH)    flMonitor; 
  // Responder     
  FrameLinkResponder #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH)  flResponder;
  // Scoreboard  
  Scoreboard #(FL_WIDTH*NUMBER_OF_WORDS)             scoreboard; 
  // Coverage                             
  Coverage #(RX_DATA_WIDTH,RX_DREM_WIDTH,TX_DATA_WIDTH,TX_DREM_WIDTH) coverage; 

  Mi32Driver                           mi32Driver;
  Mi32Transaction                      mi32Blueprint;
  tTransMbx                            mi32TransMbx;
  
  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Generator Environment
  task createGeneratorEnvironment(int packet_count = GENERATOR0_FL_PACKET_COUNT,
                          int packet_size_max[] = GENERATOR0_FL_PACKET_SIZE_MAX,
                          int packet_size_min[] = GENERATOR0_FL_PACKET_SIZE_MIN
                                  );
    // Create generator
    generator = new("Generator0", 0);
      flBlueprint = new;
      flBlueprint.packetCount   = packet_count;
      flBlueprint.packetSizeMax = packet_size_max;
      flBlueprint.packetSizeMin = packet_size_min;
      generator.blueprint       = flBlueprint;
  endtask: createGeneratorEnvironment    

  // Create Test Environment
  task createEnvironment(bit [NUMBER_OF_WORDS*FL_WIDTH-1 : 0] mask);    
      mi32TransMbx = new;

    // Create driver    
    mi32Driver  = new ("Driver MI32", mi32TransMbx, MI32_RXTX);

    flDriver  = new ("Driver0", generator.transMbx, RX);
      flDriver.txDelayEn_wt             = DRIVER0_DELAYEN_WT; 
      flDriver.txDelayDisable_wt        = DRIVER0_DELAYDIS_WT;
      flDriver.txDelayLow               = DRIVER0_DELAYLOW;
      flDriver.txDelayHigh              = DRIVER0_DELAYHIGH;
      flDriver.insideTxDelayEn_wt       = DRIVER0_INSIDE_DELAYEN_WT; 
      flDriver.insideTxDelayDisable_wt  = DRIVER0_INSIDE_DELAYDIS_WT;
      flDriver.insideTxDelayLow         = DRIVER0_INSIDE_DELAYLOW;
      flDriver.insideTxDelayHigh        = DRIVER0_INSIDE_DELAYHIGH;
    // Create monitor
    flMonitor = new ("Monitor0", MONITOR);
    // Create responder
    flResponder = new ("Responder0", TX);
      flResponder.rxDelayEn_wt            = MONITOR0_DELAYEN_WT; 
      flResponder.rxDelayDisable_wt       = MONITOR0_DELAYDIS_WT;
      flResponder.rxDelayLow              = MONITOR0_DELAYLOW;
      flResponder.rxDelayHigh             = MONITOR0_DELAYHIGH;
      flResponder.insideRxDelayEn_wt      = MONITOR0_INSIDE_DELAYEN_WT; 
      flResponder.insideRxDelayDisable_wt = MONITOR0_INSIDE_DELAYDIS_WT;
      flResponder.insideRxDelayLow        = MONITOR0_INSIDE_DELAYLOW;
      flResponder.insideRxDelayHigh       = MONITOR0_INSIDE_DELAYHIGH;    
    // Create scoreboard
    scoreboard = new;
    // Coverage class
    // V PRIPADE VIAC INTERFACOV TREBA VOLAT PRISLUSNY 
    // COVERAGE PODLA TYPU INTERFACE
    coverage = new();
      coverage.addFrameLinkInterfaceRx(RX,"RXcoverage");
      coverage.addFrameLinkInterfaceTx(MONITOR,"TXcoverage");
    // Set Callbacks
    // V PRIPADE VIAC DRIVEROV ALEBO MONITOROV TREBA VOLAT PRISLUSNE CALLBACKS
      flDriver.setCallbacks(scoreboard.driverCbs);
      flMonitor.setCallbacks(scoreboard.monitorCbs);

      scoreboard.driverCbs.mask = mask;
  endtask : createEnvironment

  task mi32_send();
      int i;
      $urandom($time);
      i = $random % NUMBER_OF_WORDS; 
      if (i < 0)
         i = -i;

      mi32Blueprint = new;
      mi32Blueprint.address = '0;
      mi32Blueprint.data    = '0;
      mi32Blueprint.data[1] = 1;
      mi32Blueprint.be      = 4'hF;
      mi32Blueprint.rw      = 1;
      mi32TransMbx.put(mi32Blueprint);
      #(2000*CLK_PERIOD);
      mi32Driver.setEnabled();
      #(2000*CLK_PERIOD);
      mi32Driver.setDisabled();

      mi32Blueprint = new;
      mi32Blueprint.randomize;
      mi32Blueprint.address = 4*(i+1);
      //mi32Blueprint.data    = '1; //HGEN_INIT[31:0];
      mi32Blueprint.be      = 4'hF;
      mi32Blueprint.rw      = 1;
      mi32TransMbx.put(mi32Blueprint);
      #(2000*CLK_PERIOD);
      mi32Driver.setEnabled();
      #(2000*CLK_PERIOD);
      mi32Driver.setDisabled();

      for(int j = 0; j < 32; j++)
         scoreboard.driverCbs.mask[i*32+j] = mi32Blueprint.data[j];

      mi32Blueprint = new;
      mi32Blueprint.address = '0;
      mi32Blueprint.data    = '0; //HGEN_INIT[31:0];
      mi32Blueprint.be      = 4'hF;
      mi32Blueprint.rw      = 1;
      mi32TransMbx.put(mi32Blueprint);
      #(2000*CLK_PERIOD);
      mi32Driver.setEnabled();
      #(2000*CLK_PERIOD);
      mi32Driver.setDisabled();
  endtask : mi32_send

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
    flDriver.setEnabled();
    flMonitor.setEnabled();
    flResponder.setEnabled();
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
     // V PRIPADE POTREBY VYPNUT VSETKY POUZITE DRIVERY A MONITORY A RESPONDERY
     // Disable drivers
     #(1000*CLK_PERIOD); 
     flDriver.setDisabled();
     // Disable monitors
     flMonitor.setDisabled();
     flResponder.setDisabled();
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
        generator.setEnabled(TRANSACTION_COUT);

        // Pokud je generator aktivni nic nedelej
        while (generator.enabled)
          #(CLK_PERIOD);


     // Disable Test Enviroment
     disableTestEnvironment();

     // Display Scoreboard
     scoreboard.display();
     coverage.display();
  endtask: test1
  
  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    // -------------------------------------
    // DESIGN ENVIROMENT
    // -------------------------------------
    bit [NUMBER_OF_WORDS*FL_WIDTH-1 : 0] value = RESET_VALUE;
    resetDesign(); // Reset design
    for(int i = 0; i < CYCLES; i++)
    begin
      createGeneratorEnvironment();
      createEnvironment(value); // Create Test Enviroment
      mi32_send();
      // -------------------------------------
      // TESTING
      // -------------------------------------
      test1();       // Run Test 1
      value = scoreboard.driverCbs.mask;
    end;
    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $stop();       // Stop testing
  end

endprogram

