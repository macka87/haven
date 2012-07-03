/* *****************************************************************************
 * Project Name: ALU Functional Verification
 * File Name:    ALU Genetic Algorithm Test Case
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         23.6.2012 
 * ************************************************************************** */
 
import test_pkg::*;
import ga_pkg::*; 
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
  
  //! Array of best chromosomes from every population
  Chromosome                                             best_chromosome[];
  
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
     aluChromosome.operandMEM_rangesMin  = OPERAND_MEM_RANGES_MIN;
     aluChromosome.operandMEM_rangesMax  = OPERAND_MEM_RANGES_MAX;
     aluChromosome.operandIMM_rangesMin  = OPERAND_IMM_RANGES_MIN;
     aluChromosome.operandIMM_rangesMax  = OPERAND_IMM_RANGES_MAX;
     
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
     $write("\n\n");
     $write("-------------------------------------------------------------------- \n");
     $write("-------------------------------------------------------------------- \n");
     $write("------------------     INITIAL GENERATION      --------------------- \n");
     $write("-------------------------------------------------------------------- \n");
     $write("-------------------------------------------------------------------- \n");
   
     foreach (population.population[i]) begin
       $write("\n\n");
       $write("--------------------------------------------------- \n");
       $write("--- INITIAL POPULATION : CHROMOSOME %d --- \n",i);
       $write("--------------------------------------------------- \n\n\n");
       simulateInitialChromosome(population.population[i]);
     end
     population.evaluate();
   endtask : evaluateInitialPopulation
   
  /*
   *  Simulate chromosome from initial population
   */ 
   task simulateInitialChromosome(Chromosome chromosome); 
     process proc;
     int coveredBins;
     int allBins;
     ALUChromosome aluChromosome;     
     
     proc = process::self(); 
     
     resetDesign();       // Reset design
     createEnvironment(); // Create Test Enviroment
     
     // Set ALU transaction parameters according to chromosome
     aluGAInCnt.setParameters(chromosome);
     
     // time measuring
     $write("START TIME: ");
     $system("date");
     
     // enable test environment
     enableTestEnvironment();
     
     // start input controller
     aluGAInCnt.start(); 
     proc.srandom(SEED1); 
     
     // generate random vectors for initial population
     aluGAInCnt.sendGenerated(TRANS_COUNT_PER_CHROM);
     
     aluGAInCnt.stop();
     
     disableTestEnvironment();
     
     // time measuring
     $write("END TIME: ");
     $system("date");
     
     // Display Scoreboard and Coverage
     scoreboard.display();
     
     coveredBins = 0;
     allBins     = 0;
     
     // Get Coverage
     aluCoverage.getCoverage(coveredBins, allBins);
     //$write("coveredBins: %d\n", coveredBins);
     //$write("allBins: %d\n", allBins);
     aluCoverage.display();
     
     // Evaluate chromosome 
     $cast(aluChromosome, chromosome); 
     aluChromosome.evaluate(coveredBins);
   endtask : simulateInitialChromosome 
   
  /*
   *  Evaluate population
   */   
   task evaluatePopulation(int generation);
     foreach (population.population[i]) begin
       $write("\n\n");
       $write("------------------------------ \n");
       $write("--- CHROMOSOME %d --- \n",i);
       $write("------------------------------ \n\n\n");
     
       simulateChromosome(generation, population.population[i]);
     end
     population.evaluate();
   endtask : evaluatePopulation 
   
  /*
   *  Simulate chromosome from new population
   */   
   task simulateChromosome(int generation, Chromosome new_chromosome);
     int coveredBins;
     int allBins;
     process proc;
     
     proc = process::self(); 
     
     resetDesign();       // Reset design
     createEnvironment(); // Create Test Enviroment
     
     // time measuring
     $write("START TIME: ");
     $system("date");
     
     // enable test environment
     enableTestEnvironment();
     
     coveredBins = 0;
     allBins     = 0;
     
     // start input controller
     aluGAInCnt.start(); 
     proc.srandom(SEED1); 
     
     // evaluate best chromosomes from old populations
     for (int i=0; i<generation; i++) begin
        // Set ALU transaction parameters according to chromosome
        aluGAInCnt.setParameters(best_chromosome[i]);  
        
        // generate random vectors for initial population
        aluGAInCnt.sendGenerated(TRANS_COUNT_PER_CHROM);
     end
     
     // evaluate chromosome from new population
     // set ALU transaction parameters according to chromosome
     aluGAInCnt.setParameters(new_chromosome);  
        
     // generate random vectors for initial population
     aluGAInCnt.sendGenerated(TRANS_COUNT_PER_CHROM);
    
     aluGAInCnt.stop();
     
     disableTestEnvironment();
     
     // time measuring
     $write("END TIME: ");
     $system("date");
     
     // Display Scoreboard and Coverage
     scoreboard.display();
     
     //coveredBins = 0;
     // allBins     = 0;
     
     // Get Coverage
     aluCoverage.getCoverage(coveredBins, allBins);
     //$write("coveredBins: %d\n", coveredBins);
     //$write("allBins: %d\n", allBins);
     aluCoverage.display();
     
     // Evaluate chromosome 
     $cast(aluChromosome, new_chromosome); 
     aluChromosome.evaluate(coveredBins);
   endtask : simulateChromosome    

  /*
   *  Main test part
   */
  initial begin
    
    //int counter     = 0; // time counter
    //int activeEvent = 0; // time period for activation of ACT signal, now set 
                          // to 0 for activation in the first clock cycle
    
    
    $write("\n\n########## GENETIC ALGORITHM ##########\n\n");
    
    //! Create array of best chromosomes
    best_chromosome = new[GENERATIONS];
    
    //! Create initial population
    createOrLoadInitialPopulation(POPULATION_FILENAME, LOAD_POPULATION, POPULATION_SIZE, MAX_MUTATIONS);
    
    //! Evaluate initial population
    evaluateInitialPopulation();

    //! Run evolution
    for (int generation = 1; generation <= GENERATIONS; generation++) begin
      
      $write("\n\n");
      $write("-------------------------------------------------------------------- \n");
      $write("-------------------------------------------------------------------- \n");
      $write("------------------     GENERATION %d     ------------------ \n",generation);
      $write("-------------------------------------------------------------------- \n");
      $write("-------------------------------------------------------------------- \n");
      
      //! Create next generation and select best chromosome from initial pop.
      population.selectAndReplace(best_chromosome[generation-1]);
      //best_chromosome[generation-1].display("BEST CHROMOSOME");
      //! Evaluate population
      evaluatePopulation(generation);
    end
        
    //! Save population
    //population.save(POPULATION_FILENAME);
    
    //! Display best individuum
    //population.getBestChromosomes(1, bestChrom);
    //bestChrom[0].display("Best chromosome");
    
    //! Stop testing
    $stop();       // Stop testing      
  end
  
endprogram

