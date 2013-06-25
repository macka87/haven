/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_chromosome_config.svh
 * Description:  Configuration object for ALU chromosomes.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         24.6.2013
 * ************************************************************************** */

/*!
 * \brief AluChromosomeConfig
 * 
 * This class represents the configuration object for ALU chromosomes.
 */
 
 class AluChromosomeConfig extends uvm_object;
    
   //! UVM Factory Registration Macro
   `uvm_object_utils(AluChromosomeConfig)
   
  /*! 
   * Data Members
   */  
   
   //! Configured items
   byte unsigned movi_values       = 3;   // num. of values for MOVI
   byte unsigned operation_values  = 16;  // num. of values for OPERATION
    
   //! Constants for generation (number of ranges for some interface signals)
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
   extern function new(string name = "AluChromosomeConfig");
   
 endclass: AluChromosomeConfig