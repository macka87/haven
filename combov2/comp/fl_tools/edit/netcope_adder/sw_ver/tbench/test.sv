/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    test.sv - test cases
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */ 
 
import test_pkg::*;
import sv_basic_comp_pkg::*;
import sv_fl_pkg::*;

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
  
  //! Controller of generated input  
  FrameLinkGenInputController #(DATA_WIDTH)  flGenInCnt; 
  //! Software driver   
  FrameLinkDriver #(DATA_WIDTH, DREM_WIDTH)  swFlDriver;   
  //! Hardware sender                        
  FrameLinkSender                            hwFlSender; 
  //! Mailbox for Input controller's transactions
  tTransMbx                                  inputMbx; 
     
  /*
   *  Environment tasks 
   */  
  
  // Create Test Environment
  task createEnvironment(); 
     //! Create input controller 
     flGenInCnt = new(GENERATOR_FL_FRAME_COUNT, GENERATOR_FL_PART_SIZE_MAX,
                      GENERATOR_FL_PART_SIZE_MIN,
                      DRIVER_BT_DELAY_EN_WT, DRIVER_BT_DELAY_DI_WT,
                      DRIVER_BT_DELAY_LOW, DRIVER_BT_DELAY_HIGH,
                      DRIVER_IT_DELAY_EN_WT, DRIVER_IT_DELAY_DI_WT,
                      DRIVER_IT_DELAY_LOW, DRIVER_IT_DELAY_HIGH
                      );
     //! Create software driver
     swFlDriver   = new("Software FrameLink Driver", flGenInCnt.transMbx, RX); 
     
     //! Create Input Mailbox
     inputMbx = new(0);          
           
     //! Create hardware sender
     hwFlSender   = new("Hardware FrameLink Sender", 0, flGenInCnt.transMbx,
                         inputMbx);           
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
    
    // software framework
    if (FRAMEWORK == 0) begin
      swFlDriver.setEnabled();
    end
    
    // hardware framework
    else if (FRAMEWORK == 1) begin
      hwFlSender.setEnabled();
    end  
     
  endtask : enableTestEnvironment

  // Disable test Environment
  task disableTestEnvironment();
    int i=0; 
     
    // software framework
    if (FRAMEWORK == 0) begin
      while (i<SIM_DELAY) begin
        if (swFlDriver.busy) i=0;
        else i++;
        #(CLK_PERIOD); 
      end
    
      swFlDriver.setDisabled();
    end
    
    // hardware framework
    else if (FRAMEWORK == 1) begin
      while (i<SIM_DELAY) begin
        if (hwFlSender.busy) i=0;
        else i++;
        #(CLK_PERIOD); 
      end
    
      hwFlSender.setDisabled();
    end
  endtask : disableTestEnvironment

  /*
   *  Test cases
   */

  // Test Case 1
  task test1();
     $write("\n\n############ TEST CASE 1 ############\n\n");
     
     // Enable Test environment
     enableTestEnvironment();
    
     // Sending of transactions
     flGenInCnt.sendGenerated(TRANSACTION_COUT);
     
     // Disable Test Enviroment
     disableTestEnvironment();

     // Display Scoreboard and Coverage
     //scoreboard.display();
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

