/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    chromosome_config.svh
 * Description:  Configuration object for chromosomes.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         14.5.2013
 * ************************************************************************** */

/*!
 * \brief ChromosomeConfig
 * 
 * This class represents the configuration object for chromosomes.
 */
 
 class ChromosomeConfig extends uvm_object;
    
   //! UVM Factory Registration Macro
   `uvm_object_utils(ChromosomeConfig)
   
  /*! 
   * Data Members
   */  
   
   int unsigned fitness         = 0;    // fitness function
   real         relativeFitness = 0;    // relative fitness function
   
  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "ChromosomeConfig");
   
 endclass: ChromosomeConfig
 
 
 
/*! 
 * Constructor - creates the ChromosomeConfig object  
 */
 function ChromosomeConfig::new(string name = "ChromosomeConfig");
   super.new(name);
 endfunction: new 