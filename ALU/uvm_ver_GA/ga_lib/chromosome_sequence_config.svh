/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    chromosome_sequence_config.svh
 * Description:  Configuration object for Chromosome Sequence.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         24.6.2013
 * ************************************************************************** */

/*!
 * \brief ChromosomeSequenceConfig
 * 
 * This class represents the configuration object for Chromosome Sequence.
 */
 
 class ChromosomeSequenceConfig extends uvm_object;
    
   //! UVM Factory Registration Macro
   `uvm_object_utils(ChromosomeSequenceConfig)
   
  /*! 
   * Data Members
   */  
   
   // POPULATION PARAMETERS
   int          populationSize  = 10;   // Size of a population
   selection_t  selection       = PROPORTIONATE; // Selection type 
   bit elitism                  = 1;    // Elitism enable by default 
   int unsigned maxMutations    = 20;   // Maximum number of mutations
   int unsigned crossoverProb   = 80;   // Crossover probability
   
   // CHROMOSOME PARAMETERS
   int unsigned fitness         = 0;    // fitness function
   real         relativeFitness = 0;    // relative fitness function
   
  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "ChromosomeSequenceConfig");
   
 endclass: ChromosomeSequenceConfig
 
 
 
/*! 
 * Constructor - creates the ChromosomeSequenceConfig object  
 */
 function ChromosomeSequenceConfig::new(string name = "ChromosomeSequenceConfig");
   super.new(name);
 endfunction: new 