/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    test.sv - test cases
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */ 
 
import test_pkg::*;

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
  // Transaction 
  FrameLinkTransaction  flBlueprint;
  // Generator
  Generator             generator; 
 
  /*
   *  Environment tasks 
   */  
  
  // Create Generator Environment
  task createGeneratorEnvironment();
  endtask: createGeneratorEnvironment    

  // Create Test Environment
  task createEnvironment();    
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
    
     /*  v tejto casti bude pravdepodobne volanie input controllerov
     // Run generators
     generator.setEnabled(TRANSACTION_COUT);

     // Do nothing while the generator is enabled
     while (generator.enabled)
       #(CLK_PERIOD);
     */
     
     // Disable Test Enviroment
     disableTestEnvironment();

     // Display Scoreboard and Coverage
     scoreboard.display();
     coverage.display();
  endtask: test1

  /*
   *  Main test part
   */
  initial begin
    // Design Environment
    resetDesign();                      
    createGeneratorEnvironment();       
    createEnvironment();                
    
    // Testing
    test1();      
        
    // Stop testing
    $stop();       
  end
endprogram

