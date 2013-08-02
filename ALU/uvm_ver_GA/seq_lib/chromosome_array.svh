/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    chromosome_sequence_config.svh
 * Description:  Configuration object for Chromosome Sequence.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         2.8.2013
 * ************************************************************************** */

/*!
 * \brief ChromosomeArray
 * 
 * This class represents an array of chromosomes.
 */
 
 class ChromosomeArray extends uvm_object;
    
   //! UVM Factory Registration Macro
   `uvm_object_utils(ChromosomeArray)
   
  /*! 
   * Data Members
   */  
   
   AluChromosome  alu_chromosome[];  // ALU Chromosomes
       
  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "ChromosomeArray");
   
 endclass: ChromosomeArray
 
 
 
/*! 
 * Constructor - creates the ChromosomeArray object  
 */
 function ChromosomeArray::new(string name = "ChromosomeArray");
   super.new(name);
 endfunction: new 