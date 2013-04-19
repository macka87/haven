/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_test.sv
 * Description:  UVM Test for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

/*! 
 * Constructor - creates the AluTest object  
 */
 function AluTest::new(string name = "AluTest", uvm_component parent = null);
   super.new(name, parent);
 endfunction: new



/*! 
 * Build - test configuration
 */ 
 function void AluTest::build_phase(uvm_phase phase);
   super.build_phase(phase);
 endfunction: build_phase



/*! 
 * Main - Stimuli are generated and applied to the DUT
 */     
 task AluTest::main_phase(uvm_phase phase);
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
    
 endtask: main_phase