/* \file test.sv
 * \brief TAG SEQUENCER Module automatic test
 * \author Marek Santa <xsanta06@stud.fit.vutbr.cz> 
 * \date 2010
 */
/*
 * Copyright (C) 2010 CESNET
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
 * $Id: test.sv 14346 2010-07-13 13:38:11Z xsanta06 $
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import math_pkg::*;
import sv_tag_sequencer_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  output logic              RESET,
  input  logic              CLK,
  iTagSequencerUsr.tb       USR,
  iTagSequencerUsr.op_tb    USR_OP,
  iTagSequencerEp.tb        EP,
  iTagSequencerEp.op_tb     EP_OP
  );
  
  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  //! TAG Transaction
  TagTransaction #(USR_TAG_WIDTH) tagBlueprint; 
  //! TAG Generator                            
  Generator                       tagGenerator;
  //! TAG Driver                               
  TagDriver      #(USR_TAG_WIDTH) tagDriver;
  //! TAG monitor                               
  TagMonitor     #(USR_TAG_WIDTH) tagMonitor;
  //! TAG Endpoint                               
  TagEndpoint    #(EP_TAG_WIDTH)  tagEndpoint;
  //! Scoreboard  
  TagScoreboard #(USR_TAG_WIDTH, TR_TABLE_FIRST_ONLY) tagScoreboard; 
  
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
    tagGenerator = new("TAG Generator", 0);
      tagBlueprint = new;
      tagGenerator.blueprint = tagBlueprint;

    // Create scoreboard
    tagScoreboard = new("TAG Scoreboard");   

    // Create drivers
    tagDriver = new ("TAG Driver", tagGenerator.transMbx, USR);
      tagDriver.setCallbacks(tagScoreboard.driverCbs);
      tagDriver.delayEn_wt          = DRIVER_DELAYEN_WT; 
      tagDriver.delayDisable_wt     = DRIVER_DELAYDIS_WT;
      tagDriver.delayLow            = DRIVER_DELAYLOW;
      tagDriver.delayHigh           = DRIVER_DELAYHIGH;

    // Create monitors
    tagMonitor = new("TAG Monitor", USR_OP);
      tagMonitor.setCallbacks(tagScoreboard.monitorCbs);

    // Create endpoint
    tagEndpoint = new ("TAG Endpoint", EP, EP_OP);
      tagEndpoint.rxDelayEn_wt          = EP_DELAYEN_WT; 
      tagEndpoint.rxDelayDisable_wt     = EP_DELAYDIS_WT;
      tagEndpoint.rxDelayLow            = EP_DELAYLOW;
      tagEndpoint.rxDelayHigh           = EP_DELAYHIGH;
      tagEndpoint.txDelayEn_wt          = EP_OP_DELAYEN_WT; 
      tagEndpoint.txDelayDisable_wt     = EP_OP_DELAYDIS_WT;
      tagEndpoint.txDelayLow            = EP_OP_DELAYLOW;
      tagEndpoint.txDelayHigh           = EP_OP_DELAYHIGH;
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
    tagDriver.setEnabled();
      
    // Enable endpoint
    tagEndpoint.setEnabled();
      
    // Enable monitors
    tagMonitor.setEnabled();

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
    tagDriver.setDisabled();

    // Disable endpoint
    tagEndpoint.setDisabled();

//    // Check if monitor is not receiving transaction for 100 CLK_PERIODs
//    i = 0;
//    while (i<100) begin
//      busy = 0;
//      for (int j=0; j < XGMII_COUNT; j++)
//        if (xgmiiMonitor[j].busy) begin
//          busy = 1;
//          break;
//        end
//
//      if (busy)
//        i = 0;
//      else i++;
//      #(CLK_PERIOD); 
//    end

    // Disable monitors     
    tagMonitor.setDisabled();

  endtask : disableTestEnvironment

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
    // Enable Test environment
    enableTestEnvironment();
    
    // Enable Generators and generate transactions
    tagGenerator.setEnabled(TRANSACTION_COUNT);
    wait (tagGenerator.enabled == 0);

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    tagScoreboard.display();
  endtask: test1


  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    // Set RNG seed
    process proc;
    proc = process::self();
    proc.srandom(RNG_SEED);

    // -------------------------------------
    // DESIGN ENVIROMENT
    // -------------------------------------
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

