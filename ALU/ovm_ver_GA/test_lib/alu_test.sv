/* *****************************************************************************
 * Project Name: HAVEN - GA
 * File Name:    alu_test.sv
 * Description:  OVM Test for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         2.4.2013
 * ************************************************************************** */

/*!
 * \brief AluTest
 * 
 * This class is OVM test for ALU.
 */
 
 class AluTest extends ovm_test;
    
   // registration of test
   `ovm_component_utils(AluTest)

   // reference to the verification enviroment
   AluEnv AluEnv_h;
   
   // Array of best chromosomes from every population
   ALUChromosome chromosome_arr[];

  /*! 
   * Constructor - creates AluTest object  
   *
   * \param name     - instance name
   * \param parent   - parent class identification
   */
   function new(string name, ovm_component parent);
     super.new(name, parent);
   endfunction: new

  /*! 
   * Build - instanciates child components
   */ 
   function void build;
     super.build();
     AluEnv_h = AluEnv::type_id::create("AluEnv_h", this);
     
     //! Create array of chromosomes
     chromosome_arr = new[GENERATIONS];
   endfunction: build

  /*! 
   * Run - runs the sequence of transactions
   */     
   task run;
     string msg;
     
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
    
   endtask: run
  
 endclass: AluTest
