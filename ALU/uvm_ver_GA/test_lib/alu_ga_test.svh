/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_ga_test.svh
 * Description:  UVM GA Test for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

/*!
 * \brief AluGATest
 * 
 * This class represents UVM test for ALU.
 */
 
 class AluGATest extends AluTestBase;
    
   //! UVM Factory Registration Macro
   `uvm_component_utils(AluGATest)
   
  /*! 
   * Data Members
   */
   
   ChromosomeSequenceConfig chromosome_sequence_cfg;  // Configuration objects
   
  /*! 
   * Component Members
   */ 
   
   Population          population_sequencer; 
   
   ChromosomeSequence  chr_seq;    // sequence of chromosomes
   TransactionSequence trans_seq;  // sequence of transactions
   
   /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "AluGATest", uvm_component parent = null);
   extern function void build_phase(uvm_phase phase);
      
   // Other methods
   extern task main_phase(uvm_phase phase);
   extern function void configure_chromosome_sequence(ChromosomeSequenceConfig chromosome_sequence_cfg);
   extern task createOrLoadInitialPopulation();
   extern task evaluateInitialPopulation();
   
 endclass: AluGATest
 
 
 
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
    
   phase.raise_objection(this); 
      
   // ------------------------------------------------------------------------
   $write("\n\n########## GENETIC ALGORITHM ##########\n\n");
   
   //! Create initial population
   createOrLoadInitialPopulation();
   
   //! Evaluate initial population
   evaluateInitialPopulation();
   
   
     
   /*AluSequence seq;
   seq = AluSequence::type_id::create("seq");
   seq.start( AluEnv_h.AluSequencer_h); */
     
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
   
   phase.drop_objection(this); 
    
 endtask: main_phase
 
 
 
/*
 *  Create or load initial population.   !!! LOAD BUDE IMPLEMENTOVANY NESKOR !!!
 */  
 task AluGATest::createOrLoadInitialPopulation();
   chr_seq = ChromosomeSequence::type_id::create("chr_seq");
   trans_seq = TransactionSequence::type_id::create("trans_seq");
   
   // connect sequences to their sequencers
   chr_seq.pop_sequencer = population_sequencer;
   trans_seq.pop_sequencer = population_sequencer;
   
   $write("******************************************************************** \n");
   $write("******************     INITIAL POPULATION      ********************* \n");
   $write("******************************************************************** \n");
      
   // start the sequences
   fork
     chr_seq.start(population_sequencer);
     trans_seq.start(alu_env.alu_agent.trans_sequencer);
   join 
 endtask: createOrLoadInitialPopulation
 
 
 
/*
 *  Evaluate initial population.   
 */  
 task AluGATest::evaluateInitialPopulation();
   
 endtask: evaluateInitialPopulation 
 
 
 
/*! 
 * Function to configure population
 */ 
 function void AluGATest::configure_chromosome_sequence(ChromosomeSequenceConfig chromosome_sequence_cfg);
   
   // POPULATION parameters
   chromosome_sequence_cfg.populationSize  = POPULATION_SIZE; // Size of a population
   chromosome_sequence_cfg.selection       = RANK;            // Selection type 
   chromosome_sequence_cfg.maxMutations    = MAX_MUTATIONS;   // Maximum number of mutations   
   
   // CHROMOSOME parameters
   chromosome_sequence_cfg.fitness         = 0;    // fitness function
   chromosome_sequence_cfg.relativeFitness = 0;    // relative fitness function   
   
   // ALU CHROMOSOME parameters 
   chromosome_sequence_cfg.movi_values           = 3;   // num. of values for MOVI
   chromosome_sequence_cfg.operation_values      = 16;  // num. of values for OPERATION
   chromosome_sequence_cfg.delay_rangesMin       = DELAY_RANGES_MIN;         
   chromosome_sequence_cfg.delay_rangesMax       = DELAY_RANGES_MAX;
   chromosome_sequence_cfg.operandA_rangesMin    = OPERAND_A_RANGES_MIN;
   chromosome_sequence_cfg.operandA_rangesMax    = OPERAND_A_RANGES_MAX;
   chromosome_sequence_cfg.operandB_rangesMin    = OPERAND_B_RANGES_MIN;
   chromosome_sequence_cfg.operandB_rangesMax    = OPERAND_B_RANGES_MAX;  
   chromosome_sequence_cfg.operandMEM_rangesMin  = OPERAND_MEM_RANGES_MIN;
   chromosome_sequence_cfg.operandMEM_rangesMax  = OPERAND_MEM_RANGES_MAX;  
   chromosome_sequence_cfg.operandIMM_rangesMin  = OPERAND_IMM_RANGES_MIN;
   chromosome_sequence_cfg.operandIMM_rangesMax  = OPERAND_IMM_RANGES_MAX; 
   
 endfunction: configure_chromosome_sequence 