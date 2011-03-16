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
  
  //! Mailbox for Input controller's transactions
  tTransMbx                                              inputMbx; 
  
  //! Controller of generated input  
  FrameLinkGenInputController #(DATA_WIDTH, DREM_WIDTH)  flGenInCnt; 
       
  /*
   *  Environment tasks 
   */  
  
  // Create Test Environment
  task createEnvironment(); 
     //! Create Input Mailbox
     inputMbx = new(0);
     
     //! Create input controller 
     flGenInCnt = new(FRAMEWORK, inputMbx,
                      GENERATOR_FL_FRAME_COUNT, GENERATOR_FL_PART_SIZE_MAX,
                      GENERATOR_FL_PART_SIZE_MIN,
                      DRIVER_BT_DELAY_EN_WT, DRIVER_BT_DELAY_DI_WT,
                      DRIVER_BT_DELAY_LOW, DRIVER_BT_DELAY_HIGH,
                      DRIVER_IT_DELAY_EN_WT, DRIVER_IT_DELAY_DI_WT,
                      DRIVER_IT_DELAY_LOW, DRIVER_IT_DELAY_HIGH,
                      RX
                      );
  endtask : createEnvironment

  /*
   *  Test auxilarity procedures
   */
  
  // Resets design
  task resetDesign();
    RESET=1;                       // Init Reset variable
    #RESET_TIME     RESET = 0;     // Deactivate reset after reset_time
  endtask : resetDesign

  /*
   *  Test cases
   */

  // Test Case 1
  task test1();
     process proc;
     proc = process::self();
     
     $write("\n\n############ TEST CASE 1 ############\n\n");
     
     // Sending of transactions
     flGenInCnt.start(); 
     proc.srandom(1);             
     flGenInCnt.sendGenerated(TRANSACTION_COUT);
     flGenInCnt.waitFor(5);
     proc.srandom(2);       
     flGenInCnt.sendGenerated(TRANSACTION_COUT);
     flGenInCnt.stop();
     
     // Display Scoreboard and Coverage
     //scoreboard.display();
     //coverage.display();
  endtask: test1

  /*
   *  Main test part
   */
  initial begin
    // Set PRNG seed
    // process proc;
    // proc = process::self();
    // proc.srandom(RNG_SEED);
    
    // Design Environment
    resetDesign();                      
    createEnvironment();                
    
    // Testing
    test1();      
        
    // Stop testing
    $stop();       
  end
endprogram

