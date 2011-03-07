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
  
  // Controller of generated input  
  FrameLinkGenInputController   flGenInCnt;    
 
  /*
   *  Environment tasks 
   */  
  
  // Create Test Environment
  task createEnvironment(); 
     flGenInCnt = new(GENERATOR_FL_FRAME_COUNT, GENERATOR_FL_PART_SIZE_MAX,
                      GENERATOR_FL_PART_SIZE_MIN);
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
  endtask : enableTestEnvironment

  // Disable test Environment
  task disableTestEnvironment();
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

