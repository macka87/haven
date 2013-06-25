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
   
   // CONFIGURATION OF CHROMOSOMES AND POPULATION 
    
   // >>>>>>>>>>>>>>>>>>>>> CHROMOSOME >>>>>>>>>>>>>>>>>>>>>
   
   // create configuration object for chromosome
   chromosome_cfg = ChromosomeConfig::type_id::create("chromosome_cfg");
   
   // configure chromosome (set chromosome parameters)
   configure_chromosome(chromosome_cfg);
   
   // put configuration into the configuration space
   uvm_config_db #(ChromosomeConfig)::set(this, "*", "ChromosomeConfig", chromosome_cfg);
   
   // >>>>>>>>>>>>>>>>>>>>> ALU CHROMOSOME >>>>>>>>>>>>>>>>>>>>>
   
   // create configuration object for ALU chromosome
   alu_chromosome_cfg = AluChromosomeConfig::type_id::create("alu_chromosome_cfg");
   
   // configure ALU chromosome (set ALU chromosome parameters)
   configure_alu_chromosome(alu_chromosome_cfg);
   
   // put configuration into the configuration space
   uvm_config_db #(AluChromosomeConfig)::set(this, "*", "AluChromosomeConfig", alu_chromosome_cfg);
   
   // >>>>>>>>>>>>>>>>>>>>> CHROMOSOME_SEQUENCE >>>>>>>>>>>>>>>>>>>>>
   
   // create configuration object for chromosome sequence
   chromosome_sequence_cfg = ChromosomeSequenceConfig::type_id::create("chromosome_sequence_cfg");
   
   // configure chromosome sequence (set chromosome sequence parameters)
   configure_chromosome_sequence(chromosome_sequence_cfg);
   
   // put configuration into the configuration space
   uvm_config_db #(ChromosomeSequenceConfig)::set(this, "*", "ChromosomeSequenceConfig", chromosome_sequence_cfg);
   
   
   // >>>>>>>>>>>>>>>>>>>>> POPULATION >>>>>>>>>>>>>>>>>>>>>
   
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
   #100ns;
 
 endtask : createOrLoadInitialPopulation
 
 
 
/*! 
 * Function to configure chromosomes
 */ 
 function void AluGATest:: configure_chromosome(ChromosomeConfig chromosome_cfg);
   chromosome_cfg.fitness         = 0;    // fitness function
   chromosome_cfg.relativeFitness = 0;    // relative fitness function     
 endfunction: configure_chromosome


 
/*! 
 * Function to configure ALU chromosomes
 */ 
 function void AluGATest::configure_alu_chromosome(AluChromosomeConfig alu_chromosome_cfg);
   alu_chromosome_cfg.movi_values       = 3;   // num. of values for MOVI
   alu_chromosome_cfg.operation_values  = 16;  // num. of values for OPERATION
    
   alu_chromosome_cfg.delay_rangesMin       = 1;         
   alu_chromosome_cfg.delay_rangesMax       = 4;
   alu_chromosome_cfg.operandA_rangesMin    = 1;
   alu_chromosome_cfg.operandA_rangesMax    = 8;
   alu_chromosome_cfg.operandB_rangesMin    = 1;
   alu_chromosome_cfg.operandB_rangesMax    = 8;  
   alu_chromosome_cfg.operandMEM_rangesMin  = 1;
   alu_chromosome_cfg.operandMEM_rangesMax  = 8;  
   alu_chromosome_cfg.operandIMM_rangesMin  = 1;
   alu_chromosome_cfg.operandIMM_rangesMax  = 8;
 endfunction: configure_alu_chromosome
 
 
 
/*! 
 * Function to configure population
 */ 
 function void AluGATest::configure_chromosome_sequence(ChromosomeSequenceConfig chromosome_sequence_cfg);
   chromosome_sequence_cfg.populationSize = 10;    // Size of a population
   chromosome_sequence_cfg.selection      = RANK;  // Selection type 
   chromosome_sequence_cfg.maxMutations   = 20;    // Maximum number of mutations   
 endfunction: configure_chromosome_sequence
