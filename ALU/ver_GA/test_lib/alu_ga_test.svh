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
   * Component Members
   */
   
   AluGAAgent           alu_ga_agent;          // The agent class
   ChromosomeSequencer  chromosome_sequencer;  // sequencer for chromosomes
  
  /*
   * Virtual interfaces
   */    
   virtual iAluIn  dut_alu_in_if;  // ALU input interface
   virtual iAluOut dut_alu_out_if; // ALU output interface 
   
  /*! 
   * Channels
   */  
   mailbox #(AluChromosome) chromosomeMbx;  
   mailbox #(AluCoverageInfo) coverageMbx;
  
  /*! 
   * Data Members
   */
   AluChromosomeArray chr_array;  // Chromosomes stored into an array
   
   /*!
   * Methods
   */
   extern function new(virtual iAluIn dut_alu_in_if, virtual iAluOut dut_alu_out_if);
   extern function void create_structure();
   extern task run();
   extern task createOrLoadInitialPopulation();
   extern task configureAluChromosome(AluChromosome alu_chromosome);
 endclass: AluGATest
 


/*! 
 *  Constructor
 */
 function AluGATest::new(virtual iAluIn  dut_alu_in_if,
                         virtual iAluOut dut_alu_out_if
                         );
   this.dut_alu_in_if = dut_alu_in_if;    //! Store pointer interface 
   this.dut_alu_out_if = dut_alu_out_if;  //! Store pointer interface  
   
   chr_array = new();
 endfunction: new   


 
/*! 
 *  Constructor - create and configure environment
 */ 
 function void AluGATest::create_structure();
   // >>>>> CREATE COMPONENTS >>>>>
   chromosomeMbx  = new(1);
   coverageMbx    = new(1);
 
   chromosome_sequencer  = new(chr_array);
   alu_ga_agent = new(dut_alu_in_if, dut_alu_out_if);
   
   chromosome_sequencer.chromosomeMbx = chromosomeMbx;
   alu_ga_agent.chromosomeMbx = chromosomeMbx;
   
   chromosome_sequencer.coverageMbx = coverageMbx;
   alu_ga_agent.coverageMbx = coverageMbx;
   
 endfunction: create_structure
 


/*! 
 * Main run
 */     
 task AluGATest::run();
   // ------------------------------------------------------------------------
   $write("\n\n########## GENETIC ALGORITHM ##########\n\n");
    
   // create environment 
   create_structure(); 
   
   //! Create initial population
   createOrLoadInitialPopulation();
   
   //! Run evolution
   //for (int generation = 1; generation <= GENERATIONS; generation++) begin
     
     
   fork  
     // run sequencer
     chromosome_sequencer.run();
   
     // run environment
     alu_ga_agent.run();
   join;
   
   $stop; 
 endtask: run  


 
/*
 *  Create or load initial population.   !!! LOAD BUDE IMPLEMENTOVANY NESKOR !!!
 */  
 task AluGATest::createOrLoadInitialPopulation();
   
   $write("******************************************************************** \n");
   $write("******************     INITIAL POPULATION      ********************* \n");
   $write("******************************************************************** \n");
   
   // create random initial population
   chr_array.alu_chromosome = new[POPULATION_SIZE];
   for (int i=0; i<POPULATION_SIZE; i++) begin
     // create chromosome 
     chr_array.alu_chromosome[i] = new();
     // configure chromosome
     configureAluChromosome(chr_array.alu_chromosome[i]);
     // randomize chromosome
     assert(chr_array.alu_chromosome[i].randomize()); 
     // print chromosome
     chr_array.alu_chromosome[i].print(i, 0);     
   end 
 endtask: createOrLoadInitialPopulation
 


/*! 
 * configureAluChromosome - configure ALU Chromosome with data from the configuration object
 */ 
 task AluGATest::configureAluChromosome(AluChromosome alu_chromosome);
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
 endtask: configureAluChromosome 