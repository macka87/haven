/* *****************************************************************************
 * Project Name: FIFO Functional Verification
 * File Name:    test.sv - test cases
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */ 
 
import test_pkg::*;
import sv_basic_comp_pkg::*;
import sv_fl_pkg::*;
import sv_fl_fifo_pkg::*;

/*
 * Test output and input interfaces of DUT.
 */ 
program TEST (
  input  logic         CLK,
  output logic         RESET,
  iFrameLinkRx.tb      RX,
  iFrameLinkTx.tb      TX,
  iFrameLinkTx.monitor MONITOR,
  iFrameLinkFifo.ctrl  CTRL
  );
  
  /*
   *  Variables declaration 
   */
  
  //! Mailbox for Input controller's transactions
  tTransMbx                                              inputMbx; 
  
  //! Mailbox for Output controller's transactions
  tTransMbx                                              outputMbx;
  
  //! Sorter's mailboxes
  tTransMbx                                              mbx[];  

  //! Input Controller of generated input  
  FrameLinkGenInputController #(DATA_WIDTH, DREM_WIDTH)  flGenInCnt; 
  
  //! Input Wrapper
  InputWrapper                                           inputWrapper;  
  
  //! Output Wrapper
  OutputWrapper                                          outputWrapper; 
  
  //! Checker
  FrameLinkFifoChecker #(DATA_WIDTH, DREM_WIDTH, BLOCK_SIZE, 
                         STATUS_WIDTH, ITEMS, USE_BRAMS) flChecker;                                                       
  //! Sorter
  Sorter                                                 sorter; 
  
  //! Output Controller 
  FrameLinkOutputController                              flOutCnt;
 
  //! Assertion Checker
  //FrameLinkAssertionChecker                              assertChecker;

  //! Assertion Reporter
  FrameLinkAssertionReporter                             assertReporter;               
  
  //! Monitor                                                       
  FrameLinkMonitor #(DATA_WIDTH, DREM_WIDTH)             flMonitor;
  
  //! Scoreboard
  FIFOScoreboard                                         scoreboard; 
  
  //! Coverage
  FrameLinkCoverage #(DATA_WIDTH, DREM_WIDTH, 
                      DATA_WIDTH, DREM_WIDTH)            flCoverage;
       
  /*
   *  Environment tasks 
   */  
  
  // Create Test Environment
  task createEnvironment(); 
     //! Create scoreboard
     scoreboard = new();
     
     //! Create coverage
     flCoverage = new();
     
     //! Create Input and Output Mailbox
     inputMbx   = new(1);
     outputMbx  = new(1);
     
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
     flCoverage.addFrameLinkInterfaceRx(RX,"RX Command Coverage");
     
     //! Create Input Wrapper
     inputWrapper = new("Input Wrapper", inputMbx); 
     
     //! Create Output Wrapper
     outputWrapper = new("Output Wrapper", outputMbx); 
     
     //! Create Sorter and Output Controllers' mailboxes
     mbx = new[2];
       // FL Output Controller mailbox
       mbx[0] = new(1); 
       // Assertion Reporter mailbox
       mbx[1] = new(1);
     sorter = new(outputMbx, mbx, 2);
     
     //! Create FrameLink Output Controller
     flOutCnt = new("Output Controller", 0, mbx[0], GENERATOR_FL_FRAME_COUNT);
     flOutCnt.setCallbacks(scoreboard.outputCbs);  
     
     //! Create Assertion Checker
    // assertChecker = new("Assertion Checker", RX, TX);

     //! Create Assertion Reporter
     assertReporter = new("Assertion Reporter", 0, mbx[1]);

     //! Create Checker
     flChecker = new("Checker", RX, TX, CTRL);
     
     //! Create Monitor 
     flMonitor    = new("FrameLink Monitor", 0, MONITOR, TX);
     flMonitor.setCallbacks(scoreboard.outputCbs);  
     flCoverage.addFrameLinkInterfaceTx(MONITOR,"TX Command Coverage");
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
      //assertChecker.setEnabled();
      flChecker.setEnabled();
      flMonitor.setEnabled();
      flCoverage.setEnabled();
    end
    if (FRAMEWORK == 1) begin
      inputWrapper.setEnabled();
      outputWrapper.setEnabled();
      sorter.setEnabled();
      flOutCnt.setEnabled();
      assertReporter.setEnabled();
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
        if (flMonitor.busy) busy = 1;
      end
      
      if (FRAMEWORK == 1) begin
        if (inputWrapper.busy || (outputWrapper.counter!=TRANSACTION_COUT) || flOutCnt.busy || assertReporter.busy) busy = 1; 
      end
        
      if (busy) i = 0;
      else i++;
      #(CLK_PERIOD); 
    end
    
    if (FRAMEWORK == 0) begin
      //assertChecker.setDisabled();
      flChecker.setDisabled();
      flMonitor.setDisabled();
      flCoverage.setDisabled();
    end
    if (FRAMEWORK == 1) begin
      inputWrapper.setDisabled();
      outputWrapper.setDisabled();
      sorter.setDisabled();
      flOutCnt.setDisabled();
      assertReporter.setDisabled();
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
     //proc.srandom(SEED2);       
     //flGenInCnt.sendGenerated(TRANSACTION_COUT);
     flGenInCnt.stop();
     
     // Disable Test Enviroment
     disableTestEnvironment();
     
     // time measuring
     $write("END TIME: ");
     $system("date");
     
     // Display Scoreboard and Coverage
     scoreboard.display();
     if (FRAMEWORK == 0) begin
        flCoverage.display();
     end

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

  final begin
    if (FRAMEWORK == 0)
        scoreboard.displayTrans();
  end
endprogram

