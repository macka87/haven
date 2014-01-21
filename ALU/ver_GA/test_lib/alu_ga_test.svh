/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU
 * File Name:    alu_ga_test.svh
 * Description:  GA Test for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         21.1.2014
 * ************************************************************************** */

/*!
 * \brief AluGATest
 * 
 * This class represents GA test for ALU.
 */
 class AluGATest;  
    
  /*! 
   * Data Members
   */
   
   //ChromosomeArray          chr_array;                // Chromosomes stored into an array
   //ChromosomeSequenceConfig chromosome_sequence_cfg;  // Configuration objects
   
  /*! 
   * Component Members
   */ 
   
   //Population               population_sequencer; 
   //ChromosomeSequence       chr_seq;    // sequence of chromosomes
   //AluGATransactionSequence trans_seq;  // sequence of transactions
   
   /*!
   * Methods
   */
   
   // User-defined methods
   extern function void create_structure();
   extern task run();
   //extern function void configure_chromosome_sequence(ChromosomeSequenceConfig chromosome_sequence_cfg);
   //extern task configureAluChromosome(AluChromosome alu_chromosome); 
   //extern task createOrLoadInitialPopulation();
   //extern task evaluatePopulation();
   
 endclass: AluGATest
 
 
 
/*! 
 *  Constructor - create and configure environment
 */ 
 function void AluGATest::create_structure();
 endfunction: create_structure
 


/*! 
 * Main run
 */     
 task AluGATest::run();
   // ------------------------------------------------------------------------
   $write("\n\n########## GENETIC ALGORITHM ##########\n\n");
    
   //! Create initial population
   //createOrLoadInitialPopulation();
   
   //! Run evolution
   //for (int generation = 1; generation <= GENERATIONS; generation++) begin
     //! Evaluate population
     //evaluatePopulation();
   //end
 endtask: run  


 
/*
 *  Create or load initial population.   !!! LOAD BUDE IMPLEMENTOVANY NESKOR !!!
 */  
 /*task AluGATest::createOrLoadInitialPopulation();
   
   $write("******************************************************************** \n");
   $write("******************     INITIAL POPULATION      ********************* \n");
   $write("******************************************************************** \n");
   
   // create random initial population
   chr_array.alu_chromosome = new[POPULATION_SIZE];
   for (int i=0; i<POPULATION_SIZE; i++) begin
     // create chromosome 
     chr_array.alu_chromosome[i] = AluChromosome::type_id::create("alu_chromosome");
     // configure chromosome
     configureAluChromosome(chr_array.alu_chromosome[i]);
     // randomize chromosome
     assert(chr_array.alu_chromosome[i].randomize()); 
     // print chromosome
     chr_array.alu_chromosome[i].print(i, 0);     
   end 
   
   // save population of chromosomes into the configuration database
   uvm_config_db #(ChromosomeArray)::set(this, "*", "ChromosomeArray", chr_array); 
   
 endtask: createOrLoadInitialPopulation */
 
 
 
/*
 *  Evaluate initial population.   
 */  
 /*task AluGATest::evaluatePopulation();
   // start the sequences
   fork
     chr_seq.start(population_sequencer);
     trans_seq.start(alu_env.alu_agent.trans_sequencer);
   join 
 endtask: evaluatePopulation*/ 



/*! 
 * configureAluChromosome - configure ALU Chromosome with data from the configuration object
 */ 
 /*task AluGATest::configureAluChromosome(AluChromosome alu_chromosome);
   alu_chromosome.movi_values           = 3;   // num. of values for MOVI
   alu_chromosome.operation_values      = 16;  // num. of values for OPERATION
   alu_chromosome.delay_rangesMin       = DELAY_RANGES_MIN;         
   alu_chromosome.delay_rangesMax       = DELAY_RANGES_MAX;
   alu_chromosome.operandA_rangesMin    = OPERAND_A_RANGES_MIN;
   alu_chromosome.operandA_rangesMax    = OPERAND_A_RANGES_MAX;
   alu_chromosome.operandB_rangesMin    = OPERAND_B_RANGES_MIN;
   alu_chromosome.operandB_rangesMax    = OPERAND_B_RANGES_MAX;  
   alu_chromosome.operandMEM_rangesMin  = OPERAND_MEM_RANGES_MIN;
   alu_chromosome.operandMEM_rangesMax  = OPERAND_MEM_RANGES_MAX;  
   alu_chromosome.operandIMM_rangesMin  = OPERAND_IMM_RANGES_MIN;
   alu_chromosome.operandIMM_rangesMax  = OPERAND_IMM_RANGES_MAX;
   
   // !!! maximal length
   alu_chromosome.length = alu_chromosome.operandA_rangesMax + alu_chromosome.operandB_rangesMax + 
                           alu_chromosome.operandMEM_rangesMax + alu_chromosome.operandIMM_rangesMax + 
                           alu_chromosome.delay_rangesMax + alu_chromosome.movi_values + 
                           alu_chromosome.operation_values;
                           
   alu_chromosome.chromosome_parts     = 7;                        
 endtask: configureAluChromosome*/ 
 


/*! 
 * Function to configure population
 */ 
 /*function void AluGATest::configure_chromosome_sequence(ChromosomeSequenceConfig chromosome_sequence_cfg);
   
   // POPULATION parameters
   chromosome_sequence_cfg.populationSize  = POPULATION_SIZE; // Size of a population
   chromosome_sequence_cfg.selection       = PROPORTIONATE;   // Selection type 
   chromosome_sequence_cfg.elitism         = ELITISM;         // Elitism 
   chromosome_sequence_cfg.maxMutations    = MAX_MUTATIONS;   // Maximum number of mutations   
   chromosome_sequence_cfg.crossoverProb   = CROSSOVER_PROB;  // Crossover probability
   
   // CHROMOSOME parameters
   chromosome_sequence_cfg.fitness         = 0;    // fitness function
   chromosome_sequence_cfg.relativeFitness = 0;    // relative fitness function   
   
 endfunction: configure_chromosome_sequence*/ 