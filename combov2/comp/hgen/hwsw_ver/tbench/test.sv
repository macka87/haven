/* *****************************************************************************
 * Project Name: HGEN Functional Verification
 * File Name:    test.sv - test cases
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         24.4.2011 
 * ************************************************************************** */

import test_pkg::*;
import sv_basic_comp_pkg::*;
import sv_fl_pkg::*;
import sv_hgen_pkg::*;
import sv_mi32_pkg::*;

/*
 * Test output and input interfaces of DUT.
 */
program TEST (
  input  logic     CLK,
  output logic     RESET,
  iFrameLinkRx.tb  RX,
  iFrameLinkTx.tb  TX,
  iFrameLinkTx.monitor MONITOR,
  iMi32.tb         MI32_RXTX
  );
  
  /*
   *  Variables declaration 
   */
  
  //! Mailbox for Input controller's transactions
  tTransMbx                                              inputMbx; 
  
  //! Mailbox for Output controller's transactions
  tTransMbx                                              outputMbx; 
  
  //! MI32 Mailbox
  tTransMbx                                              mi32TransMbx;
  
  //! MI32 Driver
  Mi32Driver                                             mi32Driver;
  
  //! MI32 Transaction                                   
  Mi32Transaction                                        mi32Blueprint;
  
  //! Input Controller of generated input  
  FrameLinkGenInputController #(DATA_WIDTH, DREM_WIDTH)  flGenInCnt; 
  
  //! Input Wrapper
  InputWrapper                                           inputWrapper;  
  
  //! Output Wrapper
  OutputWrapper                                          outputWrapper; 
  
  //! Output Controller 
  FrameLinkOutputController                              flOutCnt;
  
  //! Monitor                                                       
  FrameLinkMonitor #(DATA_WIDTH, DREM_WIDTH)             flMonitor;
  
  //! Responder
  FrameLinkResponder #(DATA_WIDTH, DREM_WIDTH)           flResponder; 
  
  //! Scoreboard
  HGENScoreboard                                         scoreboard; 
       
  /*
   *  Environment tasks 
   */
  
  // Create Test Environment
  task createEnvironment(); 
     //! Create scoreboard
     scoreboard = new(FLOWID_WIDTH, HGEN_INIT, HGEN_MASK);
     
     //! Create Input and Output Mailbox
     inputMbx   = new(0);
     outputMbx  = new(0);
     
     //! Create Input Controller 
     flGenInCnt = new("Input Controller", FRAMEWORK, inputMbx,
                      GENERATOR_FL_FRAME_COUNT, GENERATOR_FL_PART_SIZE_MAX,
                      GENERATOR_FL_PART_SIZE_MIN,
                      DRIVER_BT_DELAY_EN_WT, DRIVER_BT_DELAY_DI_WT,
                      DRIVER_BT_DELAY_LOW, DRIVER_BT_DELAY_HIGH,
                      DRIVER_IT_DELAY_EN_WT, DRIVER_IT_DELAY_DI_WT,
                      DRIVER_IT_DELAY_LOW, DRIVER_IT_DELAY_HIGH,
                      RX
                      );
     flGenInCnt.setCallbacks(scoreboard.inputCbs);
     
     //! MI32 driver                 
     mi32Blueprint = new;
     mi32Blueprint.address = '0;
     mi32Blueprint.data    = HGEN_INIT[31:0];
     mi32Blueprint.be      = 4'hF;
     mi32Blueprint.rw      = 1;
      
     mi32TransMbx = new(0);
     mi32TransMbx.put(mi32Blueprint);
     
     //! Create MI32 driver    
     mi32Driver  = new ("Driver MI32", 0, mi32TransMbx, MI32_RXTX);
     mi32Driver.setCallbacks(scoreboard.mi32DriverCbs);
                       
     //! Create Input Wrapper
     inputWrapper = new("Input Wrapper", inputMbx); 
     
     //! Create Output Wrapper
     outputWrapper = new("Output Wrapper", outputMbx); 
     
     flOutCnt = new("Output Controller", 0, outputMbx, GENERATOR_FL_FRAME_COUNT);
     flOutCnt.setCallbacks(scoreboard.outputCbs);  
     
     //! Create Monitor 
     flMonitor    = new("FrameLink Monitor", 0, MONITOR);   
     flMonitor.setCallbacks(scoreboard.outputCbs);  
     
     //! Create Responder 
     flResponder  = new("FrameLink Responder", 0, TX);
       flResponder.btDelayLow   = RESPONDER_BT_DELAY_LOW;
       flResponder.btDelayHigh  = RESPONDER_BT_DELAY_HIGH;
       flResponder.itDelayLow   = RESPONDER_IT_DELAY_LOW;
       flResponder.itDelayHigh  = RESPONDER_IT_DELAY_HIGH;             
  endtask : createEnvironment
  
  /*
   *  Test auxilarity procedures
   */
  
  // Resets design
  task resetDesign();
    RESET=1;                       // Init Reset variable
    #RESET_TIME     RESET = 0;     // Deactivate reset after reset_time
  endtask : resetDesign

  // Enable test Environment
  task enableTestEnvironment();
    if (FRAMEWORK == 0) begin
      flMonitor.setEnabled();
      flResponder.setEnabled();
    end
    if (FRAMEWORK == 1) begin
      inputWrapper.setEnabled();
      outputWrapper.setEnabled();
      flOutCnt.setEnabled();
    end  
  endtask : enableTestEnvironment
  
  // Disable test Environment
  task disableTestEnvironment();
    int i;
    bit busy;

    // Check if monitors are not receiving transaction
    i = 0;
    while (i<SIM_DELAY) begin
      busy = 0;
      
      if (FRAMEWORK == 0) begin
        if (flMonitor.busy || flResponder.busy) busy = 1;
      end
      
      if (FRAMEWORK == 1) begin
        if (inputWrapper.busy || (outputWrapper.counter!=2*TRANSACTION_COUT) || flOutCnt.busy) busy = 1; 
      end
        
      if (busy) i = 0;
      else i++;
      #(CLK_PERIOD); 
    end
    
    if (FRAMEWORK == 0) begin
      flMonitor.setDisabled();
      flResponder.setDisabled();
    end
    if (FRAMEWORK == 1) begin
      inputWrapper.setDisabled();
      outputWrapper.setDisabled();
      flOutCnt.setDisabled();
    end  
  endtask : disableTestEnvironment

  /*
   *  Test cases
   */
  
  // Test Case 1
  task initcrc();
     $write("\n\n########## LOAD Bob Jenkins Hash INIT VIA MI32 ##########\n\n");
     mi32Driver.setEnabled();
     #(2000*CLK_PERIOD);
     mi32Driver.setDisabled();
  endtask: initcrc
  
  // Test Case 2
  task test2();
     process proc;
     proc = process::self();
     
     $write("\n\n############ TEST CASE 1 ############\n\n");
     
     // time measuring
     $write("START TIME: ");
     $system("date");
     
     // Enable Test environment
     enableTestEnvironment();
     
     // Sending of transactions
     flGenInCnt.start(); 
     proc.srandom(SEED1);             
     flGenInCnt.sendGenerated(TRANSACTION_COUT);
     //flGenInCnt.waitFor(5);
     proc.srandom(SEED2);       
     flGenInCnt.sendGenerated(TRANSACTION_COUT);
     flGenInCnt.stop();
     
     // Disable Test Enviroment
     disableTestEnvironment();
     
     // time measuring
     $write("END TIME: ");
     $system("date");
     
     // Display Scoreboard and Coverage
     scoreboard.display();
     //coverage.display();
  endtask: test2

  /*
   *  Main test part
   */
   initial begin
    // Design Environment
    resetDesign(); 
    createEnvironment(); 
    
    // Testing
    initcrc();
    test2();
    
    // Stop testing
    $stop();
  end
endprogram
