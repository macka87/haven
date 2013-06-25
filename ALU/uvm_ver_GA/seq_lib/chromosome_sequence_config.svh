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
   
   int          populationSize = 10;    // Size of a population
   selection_t  selection      = RANK;  // Selection type 
   int unsigned maxMutations   = 20;    // Maximum number of mutations
       
  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "ChromosomeSequenceConfig");
   
 endclass: ChromosomeSequenceConfig