/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    test.sv - test cases
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */ 
 
import test_pkg::*;
import sv_basic_comp_pkg::*;
import sv_fl_pkg::*;
import sv_netcope_adder_pkg::*;

/*
 * Test output and input interfaces of DUT.
 */ 
program TEST (
  input  logic         CLK,
  output logic         RESET,
  iFrameLinkRx.tb      RX,
  iFrameLinkTx.tb      TX,
  iFrameLinkTx.monitor MONITOR
  );
  
  /*
   *  Variables declaration 
   */
  
  //! Mailbox for Input controller's transactions
  tTransMbx                                              inputMbx; 
  
  //! Mailbox for Output controller's transactions
  tTransMbx                                              outputMbx; 
  
  //! Controller of generated input  
  FrameLinkGenInputController #(DATA_WIDTH, DREM_WIDTH)  flGenInCnt; 
  
  //! Input Wrapper
  InputWrapper                                           inputWrapper;  
  
  //! Output Wrapper
  //OutputWrapper                                          outputWrapper; 
                                                         
  //! Monitor                                                       
  FrameLinkMonitor #(DATA_WIDTH, DREM_WIDTH)             flMonitor;
  
  //! Responder
  FrameLinkResponder #(DATA_WIDTH, DREM_WIDTH)           flResponder; 
  
  //! Scoreboard
  NetCOPEAdderScoreboard #(DATA_WIDTH, 1, TR_TABLE_FIRST_ONLY)
                                                         scoreboard; 
       
  /*
   *  Environment tasks 
   */  
  
  // Create Test Environment
  task createEnvironment(); 
     //! Create scoreboard
     scoreboard = new("Scoreboard");
     
     //! Create Input and Output Mailbox
     inputMbx   = new(0);
     outputMbx  = new(0);
     
     //! Create Input Controller 
     flGenInCnt = new(FRAMEWORK, inputMbx,
                      GENERATOR_FL_FRAME_COUNT, GENERATOR_FL_PART_SIZE_MAX,
                      GENERATOR_FL_PART_SIZE_MIN,
                      DRIVER_BT_DELAY_EN_WT, DRIVER_BT_DELAY_DI_WT,
                      DRIVER_BT_DELAY_LOW, DRIVER_BT_DELAY_HIGH,
                      DRIVER_IT_DELAY_EN_WT, DRIVER_IT_DELAY_DI_WT,
                      DRIVER_IT_DELAY_LOW, DRIVER_IT_DELAY_HIGH,
                      RX
                      );
     flGenInCnt.setCallbacks(scoreboard.inputCbs); 
     
     //! Create Input Wrapper
     inputWrapper = new("Input Wrapper", inputMbx); 
     
     //! Create Output Wrapper
     //outputWrapper = new("Output Wrapper", outputMbx); 
     
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
      //outputWrapper.setEnabled();
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
        if (inputWrapper.busy) busy = 1; 
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
      //outputWrapper.setDisabled();
    end  
  endtask : disableTestEnvironment

  /*
   *  Test cases
   */

  // Test Case 1
  task test1();
     process proc;
     proc = process::self();
     
     $write("\n\n############ TEST CASE 1 ############\n\n");
     
     // Enable Test environment
     enableTestEnvironment();
     
     // Sending of transactions
     flGenInCnt.start(); 
     proc.srandom(SEED1);             
     flGenInCnt.sendGenerated(TRANSACTION_COUT);
     flGenInCnt.waitFor(5);
     proc.srandom(SEED2);       
     flGenInCnt.sendGenerated(TRANSACTION_COUT);
     flGenInCnt.stop();
     
     // Disable Test Enviroment
     disableTestEnvironment();
     
     // Display Scoreboard and Coverage
     scoreboard.display();
     //coverage.display();
  endtask: test1

  /*
   *  Main test part
   */
  initial begin
    // Design Environment
    resetDesign();                      
    createEnvironment();                
    
    // Testing
    test1();      
        
    // Stop testing
    $stop();       
  end
endprogram

