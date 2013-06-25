/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    chromosome_sequence_config.sv
 * Description:  Configuration object for Chromosome Sequence.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         24.6.2013
 * ************************************************************************** */

/*! 
 * Constructor - creates the ChromosomeSequenceConfig object  
 */
 function ChromosomeSequenceConfig::new(string name = "ChromosomeSequenceConfig");
   super.new(name);
 endfunction: new