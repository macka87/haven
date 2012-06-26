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
  
  //! Chromosome format
  ALUChromosome                                          aluChromosome;
  
  //! Population
  Population                                             population;
  
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
     aluGAInCnt = new("ALU Input Controller", FRAMEWORK, inputMbx, ALU_IN); 
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
   *  TEST PART
   */
  
  /*
   *  Create or load initial population.
   */  
   task createOrLoadInitialPopulation(string filename, 
                                      bit load, 
                                      int populationSize,
                                      int maxMutations
                                      );
    
     //! Create blueprint transaction
     aluChromosome  = new();
      
     aluChromosome.delay_rangesMin       = DELAY_RANGES_MIN;
     aluChromosome.delay_rangesMax       = DELAY_RANGES_MAX;
     aluChromosome.operandA_rangesMin    = OPERAND_A_RANGES_MIN;
     aluChromosome.operandA_rangesMax    = OPERAND_A_RANGES_MAX;
     aluChromosome.operandB_rangesMin    = OPERAND_B_RANGES_MIN;
     aluChromosome.operandB_rangesMax    = OPERAND_B_RANGES_MAX;
     aluChromosome.operandIMM_rangesMin  = OPERAND_IMM_RANGES_MIN;
     aluChromosome.operandIMM_rangesMax  = OPERAND_IMM_RANGES_MAX;
     aluChromosome.operandMEM_rangesMin  = OPERAND_MEM_RANGES_MIN;
     aluChromosome.operandMEM_rangesMax  = OPERAND_MEM_RANGES_MAX;
      
     // Create population
     population = new("Population", populationSize, maxMutations);
     population.create(aluChromosome);
    
     // Load population from file
     if (load) begin
       $write("Population loaded from file %s\n",filename);
       population.load(filename,aluChromosome);
     end
   endtask : createOrLoadInitialPopulation
    
  /*
   *  Evaluate initial population
   */   
   task evaluateInitialPopulation();
    foreach (population.population[i])
      simulateChromosome(population.population[i], i);

    //population.evaluate();
   endtask : evaluateInitialPopulation
   
  /*
   *  Simulate chromosome
   */ 
   task simulateChromosome(Chromosome chromosome, int no); 
     resetDesign();       // Reset design
     createEnvironment(); // Create Test Enviroment
     
     // Set ALU transaction parameters according to chromosome
     aluGAInCnt.setParameters(chromosome);
     
     enableTestEnvironment();
     
     //aluGAInCnt.start(); 
     
     disableTestEnvironment();
   endtask : simulateChromosome

  /*
   *  Main test part
   */
  initial begin
    process proc;
    int counter     = 0; // time counter
    int activeEvent = 0; // time period for activation of ACT signal, now set 
                          // to 0 for activation in the first clock cycle
    proc = process::self(); 
    
    $write("\n\n########## GENETIC ALGORITHM ##########\n\n");
    
    //! Create initial population
    createOrLoadInitialPopulation(POPULATION_FILENAME, LOAD_POPULATION, POPULATION_SIZE, MAX_MUTATIONS);
    
    //! Evaluate initial population
    evaluateInitialPopulation();

    //! Run evolution
    //for (int generation = 1; generation <= GENERATIONS; generation++) begin
    //  $write("## Generation: %0d ##\n",generation);
      //! Create next generation
    //  population.selectAndReplace();
      //! Evaluate population
    //  evaluatePopulation();
    //end
        
    //! Save population
    //population.save(POPULATION_FILENAME);
    
    //! Display best individuum
    //population.getBestChromosomes(1, bestChrom);
    //bestChrom[0].display("Best chromosome");
    
    //! Stop testing
    $stop();       // Stop testing      
  end
  
  
  
   
  
  
  
  // Test Case 1
  //task test1();
   //  process proc;
   //  int counter     = 0; // time counter
    // int activeEvent = 0; // time period for activation of ACT signal, now set 
                          // to 0 for activation in the first clock cycle
     //proc = process::self();
     
     //$write("\n\n############ TEST CASE 1 ############\n\n");
     
     // time measuring
    // $write("START TIME: ");
    // $system("date");
     
     // Enable Test environment
     //enableTestEnvironment();
     
     // Sending of transactions
    // aluGAInCnt.start(); 
    //proc.srandom(SEED1);     
     
     // Create initial population
     //aluGAInCnt.createOrLoadInitialPopulation(POPULATION_FILENAME, LOAD_POPULATION, POPULATION_SIZE, MAX_MUTATIONS);
    
     // Simulate each chromosome of population from simulation time 0 and //receive coverage statistics
    // foreach (aluGAInCnt.population.population[i])
    //   resetDesign(); // Reset design
    //   createEnvironment(); // Create Test Enviroment
    //   enableTestEnvironment();
    //   aluGAInCnt.simulateChromosome(aluGAInCnt.population.population[i], i);
    // aluGAInCnt.
     
     // Evaluate initial population
     //aluGAInCnt.evaluateInitialPopulation();
     
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
    // aluGAInCnt.stop();
     
     // Disable Test Enviroment
    // disableTestEnvironment();
     
     // time measuring
    // $write("END TIME: ");
     //$system("date");
     
     // Display Scoreboard and Coverage
    // scoreboard.display();
    // if (FRAMEWORK == 0) aluCoverage.display();
  //endtask: test1

  
endprogram

