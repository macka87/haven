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
   selection_t  selection       = RANK; // Selection type 
   int unsigned maxMutations    = 20;   // Maximum number of mutations
   
   // CHROMOSOME PARAMETERS
   int unsigned fitness         = 0;    // fitness function
   real         relativeFitness = 0;    // relative fitness function
   
   // ALU CHROMOSOME PARAMETERS
   byte unsigned movi_values           = 3;   // num. of values for MOVI
   byte unsigned operation_values      = 16;  // num. of values for OPERATION
   byte unsigned delay_rangesMin       = 1;         
   byte unsigned delay_rangesMax       = 4;
   byte unsigned operandA_rangesMin    = 1;
   byte unsigned operandA_rangesMax    = 8;
   byte unsigned operandB_rangesMin    = 1;
   byte unsigned operandB_rangesMax    = 8;  
   byte unsigned operandMEM_rangesMin  = 1;
   byte unsigned operandMEM_rangesMax  = 8;  
   byte unsigned operandIMM_rangesMin  = 1;
   byte unsigned operandIMM_rangesMax  = 8;
       
  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "ChromosomeSequenceConfig");
   
 endclass: ChromosomeSequenceConfig