/* *****************************************************************************
 * Project Name: ALU Functional Verification
 * File Name:    ALU Genetic Algorithm Test Case
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         23.6.2012 
 * ************************************************************************** */
 
import test_pkg::*; 
import ga_test_pkg::*;
import sv_basic_comp_pkg::*;
import sv_alu_pkg::*;

/*
 * Test output and input interfaces of DUT.
 */ 
program TEST (
  input  logic         CLK,
  iAluIn               ALU_IN,
  iAluOut              ALU_OUT
  );
  
  /*
   *  Variables declaration 
   */
  
  //! Mailbox for Input controller's transactions
  tTransMbx                                              inputMbx;
  
  //! Mailbox for Output controller's transactions
  tTransMbx                                              outputMbx; 
  
  //! Input Controller of generated input  
  ALUGAInputController #(DATA_WIDTH, GEN_INPUT, GEN_OUTPUT) aluGAInCnt;
  
  //! Input Wrapper
  InputWrapper                                           inputWrapper;  
  
  //! Output Wrapper
  OutputWrapper                                          outputWrapper; 
  
  //! Output Controller 
  ALUOutputController #(DATA_WIDTH)                      aluOutCnt;
  
  //! Monitor                                                       
  ALUMonitor #(DATA_WIDTH)                               aluMonitor;
  
  //! Scoreboard
  ALUScoreboard #(DATA_WIDTH)                            scoreboard; 
  
  //! Coverage
  ALUCoverage #(DATA_WIDTH)                              aluCoverage;
  
  /*
   *  Environment tasks 
   */  
  
  // Create Test Environment
  task createEnvironment(); 
     //! Create scoreboard
     scoreboard = new("ALU Scoreboard");
     
     //! Create coverage
     aluCoverage = new("ALU Coverage");
     
     //! Create Input and Output Mailbox
     inputMbx   = new(1);
     outputMbx  = new(1);

     //! Create Input Controller 
     aluGAInCnt = new("ALU Input Controller", FRAMEWORK, inputMbx,
                      DELAY_RANGES_MIN, DELAY_RANGES_MAX,
                      OPERAND_A_RANGES_MIN, OPERAND_A_RANGES_MAX,
                      OPERAND_B_RANGES_MIN, OPERAND_B_RANGES_MAX,
                      OPERAND_IMM_RANGES_MIN, OPERAND_IMM_RANGES_MAX,
                      OPERAND_MEM_RANGES_MIN, OPERAND_MEM_RANGES_MAX,
                      DELAY_MIN, DELAY_MAX, 
                      ALU_IN
                      ); 
     aluGAInCnt.setCallbacks(scoreboard.inputCbs); 
     aluCoverage.addInALUInterface(ALU_IN, "ALU Input Interface Coverage");
     
     //! Create Input Wrapper
     inputWrapper = new("Input Wrapper", inputMbx); 
     
     //! Create Output Wrapper
     outputWrapper = new("Output Wrapper", outputMbx); 
     
     aluOutCnt = new("Output Controller", 0, outputMbx);
     aluOutCnt.setCallbacks(scoreboard.outputCbs);  
     
     //! Create Monitor 
     aluMonitor    = new("ALU Monitor", 0, ALU_OUT);   
     aluMonitor.setCallbacks(scoreboard.outputCbs);    
     aluCoverage.addOutALUInterface(ALU_OUT,"ALU Output Interface Coverage");
  endtask : createEnvironment

  /*
   *  Test auxilarity procedures
   */
  
  // Resets design
  task resetDesign();
    ALU_IN.cb.RST <= 1;                  // Init Reset variable
    ALU_IN.cb.ACT <= 0;         // No activity during reset
    #RESET_TIME      
    ALU_IN.cb.RST <= 0; 
  endtask : resetDesign  
  
  // Enable test Environment
  task enableTestEnvironment();
    if (FRAMEWORK == 0) begin
      aluMonitor.setEnabled();
      aluCoverage.setEnabled();
    end
    if (FRAMEWORK == 1) begin
      inputWrapper.setEnabled();
      outputWrapper.setEnabled();
      aluOutCnt.setEnabled();
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
        if (aluMonitor.busy) busy = 1;
      end
      
      if (FRAMEWORK == 1) begin
        if (inputWrapper.busy || (outputWrapper.counter!=TRANSACTION_COUT) || aluOutCnt.busy) busy = 1; 
      end
        
      if (busy) i = 0;
      else i++;
      #(CLK_PERIOD); 
    end
    
    if (FRAMEWORK == 0) begin
      aluMonitor.setDisabled();
      aluCoverage.setDisabled();
    end
    if (FRAMEWORK == 1) begin
      inputWrapper.setDisabled();
      outputWrapper.setDisabled();
      aluOutCnt.setDisabled();
    end  
  endtask : disableTestEnvironment

  /*
   *  Test cases
   */

  // Test Case 1
  task test1();
     process proc;
     int counter     = 0; // time counter
     int activeEvent = 0; // time period for activation of ACT signal, now set 
                          // to 0 for activation in the first clock cycle
     proc = process::self();
     
     $write("\n\n############ TEST CASE 1 ############\n\n");
     
     // time measuring
     $write("START TIME: ");
     $system("date");
     
     // Enable Test environment
     enableTestEnvironment();
     
     // Sending of transactions
     aluGAInCnt.start(); 
     proc.srandom(SEED1);     
     // Create initial population
     aluGAInCnt.createOrLoadInitialPopulation(POPULATION_FILENAME, LOAD_POPULATION, POPULATION_SIZE, MAX_MUTATIONS);
     // Evaluate initial population
     //aluGAInCnt.evaluatePopulation();
     
     // Run evolution
     //for (int generation = 1; generation <= GENERATIONS; generation++) begin
     //  $write("## Generation: %0d ##\n",generation);
       // Create next generation
     //  aluGAInCnt.createNextPopulation();
       // Evaluate population
     //  aluGAInCnt.evaluatePopulation();
     //end
     
     // Save population
     //aluGAInCnt.savePopulation(POPULATION_FILENAME);
     // Display best individuum
     //aluGAInCnt.displayBestChromosomes;

     // Stop genetic algorithm
     aluGAInCnt.stop();
     
     // Disable Test Enviroment
     disableTestEnvironment();
     
     // time measuring
     $write("END TIME: ");
     $system("date");
     
     // Display Scoreboard and Coverage
     scoreboard.display();
     if (FRAMEWORK == 0) aluCoverage.display();
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

