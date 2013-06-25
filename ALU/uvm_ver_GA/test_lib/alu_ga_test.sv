/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_ga_test.sv
 * Description:  UVM GA Test for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

/*! 
 * Constructor - creates the AluGATest object  
 */
 function AluGATest::new(string name = "AluGATest", uvm_component parent = null);
   super.new(name, parent);
 endfunction: new



/*! 
 * Build - test configuration
 */ 
 function void AluGATest::build_phase(uvm_phase phase);
   super.build_phase(phase);
   
   // CONFIGURATION OF CHROMOSOMES IN SEQUENCE
    
   // create configuration object for chromosome sequence
   chromosome_sequence_cfg = ChromosomeSequenceConfig::type_id::create("chromosome_sequence_cfg");
   
   // configure chromosome sequence (set chromosome sequence parameters)
   configure_chromosome_sequence(chromosome_sequence_cfg);
   
   // put configuration into the configuration space
   uvm_config_db #(ChromosomeSequenceConfig)::set(this, "*", "ChromosomeSequenceConfig", chromosome_sequence_cfg);
   
   
   // POPULATION 
   
   // create Population Sequencer
   population_sequencer = Population::type_id::create("population_sequencer", this);
   
 endfunction: build_phase



/*! 
 * Main - Stimuli are generated and applied to the DUT
 */     
 task AluGATest::main_phase(uvm_phase phase);
   string msg;
      
   // ------------------------------------------------------------------------
   $write("\n\n########## GENETIC ALGORITHM ##########\n\n");
   
   //! Create initial population
   createOrLoadInitialPopulation();
   
   
     
   /*AluSequence seq;
   seq = AluSequence::type_id::create("seq");
   seq.start( AluEnv_h.AluSequencer_h); */
     
   // ------------------------------------------------------------------------
   $write("\n\n########## GENETIC ALGORITHM ##########\n\n");
     
   //! Create initial population
   //createOrLoadInitialPopulation(POPULATION_FILENAME, LOAD_POPULATION, POPULATION_SIZE, MAX_MUTATIONS);
    
   //! Evaluate initial population
   //evaluateInitialPopulation();
     
   //! Run evolution
   //for (int generation = 1; generation <= GENERATIONS; generation++) begin
       
     //! Create next generation and select best chromosome from initial population
     //population.selectAndReplace(chromosome_arr[generation-1]);
     //chromosome_arr[generation-1].display("BEST CHROMOSOME");
       
     //! Evaluate population
     //evaluatePopulation(generation);
   //end
     
   //! Save population
   //population.save(POPULATION_FILENAME);
    
   //! Display best individuum from population
   //population.getBestChromosomes(1, bestChrom);
   //bestChrom[0].display("Best chromosome");
    
 endtask: main_phase
 
 
 
/*
 *  Create or load initial population.   !!! LOAD BUDE IMPLEMENTOVANY NESKOR !!!
 */  
 task AluGATest::createOrLoadInitialPopulation();
   ChromosomeSequence chrom_seq;  // sequence of chromosomes
 
   chrom_seq = ChromosomeSequence::type_id::create("chrom_seq");
   chrom_seq.start(population_sequencer);
    
 endtask : createOrLoadInitialPopulation
 
 
 
/*! 
 * Function to configure population
 */ 
 function void AluGATest::configure_chromosome_sequence(ChromosomeSequenceConfig chromosome_sequence_cfg);
   
   // POPULATION parameters
   chromosome_sequence_cfg.populationSize  = 3;    // Size of a population
   chromosome_sequence_cfg.selection       = RANK; // Selection type 
   chromosome_sequence_cfg.maxMutations    = 20;   // Maximum number of mutations   
   
   // CHROMOSOME parameters
   chromosome_sequence_cfg.fitness         = 0;    // fitness function
   chromosome_sequence_cfg.relativeFitness = 0;    // relative fitness function   
   
   // ALU CHROMOSOME parameters 
   chromosome_sequence_cfg.movi_values           = 3;   // num. of values for MOVI
   chromosome_sequence_cfg.operation_values      = 16;  // num. of values for OPERATION
   chromosome_sequence_cfg.delay_rangesMin       = 1;         
   chromosome_sequence_cfg.delay_rangesMax       = 4;
   chromosome_sequence_cfg.operandA_rangesMin    = 1;
   chromosome_sequence_cfg.operandA_rangesMax    = 8;
   chromosome_sequence_cfg.operandB_rangesMin    = 1;
   chromosome_sequence_cfg.operandB_rangesMax    = 8;  
   chromosome_sequence_cfg.operandMEM_rangesMin  = 1;
   chromosome_sequence_cfg.operandMEM_rangesMax  = 8;  
   chromosome_sequence_cfg.operandIMM_rangesMin  = 1;
   chromosome_sequence_cfg.operandIMM_rangesMax  = 8; 
   
 endfunction: configure_chromosome_sequence
