/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_chromosome_config.sv
 * Description:  Configuration object for ALU chromosomes.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         24.6.2013
 * ************************************************************************** */

/*! 
 * Constructor - creates the AluChromosomeConfig object  
 */
 function AluChromosomeConfig::new(string name = "AluChromosomeConfig");
   super.new(name);
 endfunction: new