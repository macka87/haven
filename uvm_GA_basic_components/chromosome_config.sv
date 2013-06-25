/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    chromosome_config.sv
 * Description:  Configuration object for chromosomes.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         14.5.2013
 * ************************************************************************** */

/*! 
 * Constructor - creates the ChromosomeConfig object  
 */
 function ChromosomeConfig::new(string name = "ChromosomeConfig");
   super.new(name);
 endfunction: new