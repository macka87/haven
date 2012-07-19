/* *****************************************************************************
 * Project Name: HGEN Functional Verification
 * File Name:    test.sv - test cases
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         24.4.2011 
 * ************************************************************************** */

import test_pkg::*;
import sv_basic_comp_pkg::*;
import sv_fl_pkg::*;
import sv_types_pkg::*; 
import sv_hgen_pkg::*;
import sv_mi32_pkg::*;
import dpi_wrapper_pkg::*;

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
  
  //! Mailbox for transactions generated in HW
  tTransMbx                                              genMbx; 
  
  //! Sorter's mailboxes
  tTransMbx                                              mbx[];  

  //! MI32 Transaction                                   
  MI32Transaction                                        mi32Trans;
  
  //! MI23 Input Controller 
  MI32InputController                                    mi32InCnt;
  
  //! FrameLink Input Controller of generated input  
  FrameLinkGenInputController #(DATA_WIDTH, DREM_WIDTH, 
                                GEN_INPUT, GEN_OUTPUT)   flGenInCnt;  
  
  //! Input Wrapper
  InputWrapper                                           inputWrapper;  
  
  //! Output Wrapper
  OutputWrapper                                          outputWrapper; 
  
  //! Sorter
  Sorter                                                 sorter; 
  
  //! Output Controller 
  FrameLinkOutputController                              flOutCnt;
  
  //! Generator Output Controller
  FrameLinkGenOutputController #(DATA_WIDTH)             flGenOutCnt;
  
  //! Assertion Reporter
  FrameLinkAssertionReporter                             assertReporter;               
  
  //! Signal Reporter
  //FrameLinkSignalReporter #(DATA_WIDTH)                  sigReporter;
  
  //! Coverage Reporter
  //FrameLinkCoverageReporter                              covReporter;
  
  //! Monitor                                                       
  FrameLinkMonitor #(DATA_WIDTH, DREM_WIDTH)             flMonitor;
  
  //! Scoreboard
  HGENScoreboard                                         scoreboard; 
  
  //! Coverage
  FrameLinkCoverage #(DATA_WIDTH, DREM_WIDTH, 
                      DATA_WIDTH, DREM_WIDTH)            flCoverage;
       
  /*
   *  Environment tasks 
   */
  
  // Create Test Environment
  task createEnvironment(); 
     //! Create scoreboard
     scoreboard = new(FLOWID_WIDTH, HGEN_INIT, HGEN_MASK);
     
     //! Create coverage
     flCoverage = new();
     
     //! Create Input and Output Mailbox
     inputMbx   = new(1);
     outputMbx  = new(1);
     genMbx     = new(1);
     
     //! Create MI32 Input Controller
     mi32InCnt = new("MI32 Input Controller", FRAMEWORK, inputMbx, MI32_RXTX);
     mi32InCnt.setCallbacks(scoreboard.mi32DriverCbs); 
     
     //! Create FrameLink Input Controller 
     flGenInCnt = new("FrameLink Input Controller", FRAMEWORK, inputMbx, genMbx,
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
     mbx = new[5];
       // FL Output Controller mailbox
       mbx[0] = new(0);
       // FL Generator Output Controller mailbox
       mbx[1] = new(1); 
       // Assertion Reporter mailbox
       mbx[2] = new(1);
       // Signal Reporter
       mbx[3] = new(1);
       // Coverage Reporter
       mbx[4] = new(1);
       
     sorter = new(outputMbx, mbx, 5);
     
     flOutCnt = new("Output Controller", 0, mbx[0], GENERATOR_FL_FRAME_COUNT);
     flOutCnt.setCallbacks(scoreboard.outputCbs);  
     
     //! Create FrameLink Generator Output Controller
     flGenOutCnt = new("Generator Output Controller", 0, mbx[1], genMbx, GENERATOR_FL_FRAME_COUNT);
     
     //! Create Assertion Reporter
     assertReporter = new("Assertion Reporter", 0, mbx[2], CLK_PERIOD, RESET_TIME);

     //! Create Signal Reporter
     //sigReporter = new("Signal Reporter", 0, mbx[3], CLK_PERIOD, RESET_TIME);

     //! Create Coverage Reporter
     //covReporter = new("Coverage Reporter", 0, mbx[4], CLK_PERIOD, RESET_TIME);

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
    int res;
  
    priority case (FRAMEWORK)
      SW_FULL     : begin
                      flMonitor.setEnabled();
                      flCoverage.setEnabled();
                    end
      SW_DES_HW_G : begin
                      // Open channel for data generated in HW
                      res = c_openDMAChannel();  
                      $write("OPENING DMA CHANNEL (expected 0): %d\n",res); 
                      outputWrapper.setEnabled();
                      sorter.setEnabled();
                      flGenOutCnt.setEnabled();
                      flMonitor.setEnabled();
                      flCoverage.setEnabled();
                    end 
      SW_ES_HW_GD : begin
                      // Open channel for data generated in HW
                      res = c_openDMAChannel();  
                      $write("OPENING DMA CHANNEL (expected 0): %d\n",res); 
                      outputWrapper.setEnabled();
                      sorter.setEnabled();
                      flGenOutCnt.setEnabled();
                      flOutCnt.setEnabled();
                      assertReporter.setEnabled();
                      //sigReporter.setEnabled();
                    end 
      SW_GES_HW_D : begin
                      inputWrapper.setEnabled();
                      outputWrapper.setEnabled();
                      sorter.setEnabled();
                      flOutCnt.setEnabled();
                      assertReporter.setEnabled();
                      //sigReporter.setEnabled();
                    end
      HW_FULL     : begin
                      // Open channel for data generated in HW
                      res = c_openDMAChannel();  
                      $write("OPENING DMA CHANNEL (expected 0): %d\n",res); 
                      outputWrapper.setEnabled();
                      sorter.setEnabled();
                      assertReporter.setEnabled();
                    end              
                    
    endcase   
  endtask : enableTestEnvironment
  
  // Disable test Environment
  task disableTestEnvironment();
    int i, res;
    bit busy;

    // Check if monitors are not receiving transaction
    i = 0;
    while (i<SIM_DELAY) begin
      busy = 0;
      
      priority case (FRAMEWORK)
        SW_FULL     : if (flMonitor.busy) busy = 1; 
        SW_DES_HW_G : if (flMonitor.busy) busy = 1; 
        SW_ES_HW_GD : if (flOutCnt.busy || assertReporter.busy) busy = 1; 
        SW_GES_HW_D : if (inputWrapper.busy || (flOutCnt.counter<TRANSACTION_COUNT) || assertReporter.busy) busy = 1; 
        HW_FULL     : if (assertReporter.busy) busy = 1; 
      endcase 
      
     /* $write("Looping at time %t ps\n", $time);
      $write("InputWrapper busy: %d\n", inputWrapper.busy);
      $write("OutputWrapper counter: %d/%d\n", outputWrapper.counter,
        TRANSACTION_COUNT);
      $write("FlOutCnt busy: %d\n", flOutCnt.busy);
      $write("AssertReporter busy: %d\n", assertReporter.busy);
      $write("SignalReporter busy: %d\n", sigReporter.busy);
      $write("--------------------------------------------------\n");*/

      if (busy) i = 0;
      else i++;
      
      priority case (FRAMEWORK)
        SW_FULL     : #(CLK_PERIOD);
        SW_DES_HW_G : #(CLK_PERIOD);
        SW_ES_HW_GD : #(CLK_PERIOD);
        SW_GES_HW_D : #1ps; 
        HW_FULL     : #1ps; 
      endcase 
    end
    
    priority case (FRAMEWORK)
      SW_FULL     : begin
                      flMonitor.setDisabled();
                      flCoverage.setDisabled();
                    end
      SW_DES_HW_G : begin
                      outputWrapper.setDisabled();
                      sorter.setDisabled();
                      flGenOutCnt.setDisabled();
                      flMonitor.setDisabled();
                      flCoverage.setDisabled();
                      res = c_closeDMAChannel();  
                      $write("CLOSING CHANNEL (expected 0): %d\n",res);
                    end  
      SW_ES_HW_GD : begin
                      outputWrapper.setDisabled();
                      sorter.setDisabled();
                      flGenOutCnt.setDisabled();
                      flOutCnt.setDisabled();
                      assertReporter.setDisabled();
                      //sigReporter.setDisabled();
                      res = c_closeDMAChannel();  
                      $write("CLOSING CHANNEL (expected 0): %d\n",res);
                    end              
      SW_GES_HW_D : begin
                      inputWrapper.setDisabled();
                      outputWrapper.setDisabled();
                      sorter.setDisabled();
                      flOutCnt.setDisabled();
                      assertReporter.setDisabled();
                      //sigReporter.setDisabled();
                    end
      HW_FULL     : begin
                      outputWrapper.setDisabled(); 
                      sorter.setDisabled();
                      assertReporter.setDisabled();
                      res = c_closeDMAChannel();  
                      $write("CLOSING CHANNEL (expected 0): %d\n",res);
                    end              
    endcase 
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
     $system("date +%s.%N");
     
     // Enable Test environment
     enableTestEnvironment();
     
     // --- Initialization through MI32 ---
     
     //! Init MI32 transaction                 
     mi32Trans = new;
     mi32Trans.address = '0;
     mi32Trans.data    = HGEN_INIT[31:0];
     mi32Trans.be      = 4'hF;
     mi32Trans.rw      = 1;
     mi32Trans.btDelayEn_wt  = DRIVER_BT_DELAY_EN_WT;
     mi32Trans.btDelayDi_wt  = DRIVER_BT_DELAY_DI_WT;
     mi32Trans.btDelayLow    = DRIVER_BT_DELAY_LOW;
     mi32Trans.btDelayHigh   = DRIVER_BT_DELAY_HIGH;
     
     assert(randomize());           //! randomize random values  
          
     mi32InCnt.start(); 
     mi32InCnt.sendTransaction(mi32Trans);
     mi32InCnt.stop();
    
     // --- Sending of FRAMELINK transactions ---
     
     if (FRAMEWORK == HW_FULL) begin
       flGenInCnt.sendGenerated(TRANSACTION_COUNT);
       flGenInCnt.stop();
       flGenInCnt.checkScoreboard(TRANSACTION_COUNT);
     end   
     else begin  
       // Sending of transactions
       flGenInCnt.start(); 
       proc.srandom(SEED1);             
       flGenInCnt.sendGenerated(TRANSACTION_COUNT);
       //flGenInCnt.stop();
     end
     
     // Disable Test Enviroment
     disableTestEnvironment();
     
     // time measuring
     $write("END TIME: ");
     $system("date +%s.%N");
     
     // Display Scoreboard and Coverage
     if (FRAMEWORK != HW_FULL) scoreboard.display();
     if (FRAMEWORK == SW_FULL || FRAMEWORK == SW_DES_HW_G) flCoverage.display();
     //if (FRAMEWORK == HW_FULL) covReporter.display();
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
  
  // final section for assertion reports
  final begin
	  int res;
    
    priority case (FRAMEWORK)
       SW_FULL     : scoreboard.displayTrans();
       SW_DES_HW_G : scoreboard.displayTrans();
       SW_ES_HW_GD : begin
                       res = c_closeDMAChannel();  
                       $write("CLOSING CHANNEL (musi byt 0): %d\n",res);
                     end 
       SW_GES_HW_D : begin
                       res = c_closeDMAChannel();  
                       $write("CLOSING CHANNEL (musi byt 0): %d\n",res);
                     end 
       HW_FULL     : begin
                       res = c_closeDMAChannel();  
                       $write("CLOSING CHANNEL (musi byt 0): %d\n",res);
                     end
     endcase   
  end
endprogram

