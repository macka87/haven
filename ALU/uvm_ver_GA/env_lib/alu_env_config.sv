/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_env_config.sv
 * Description:  Configuration object for the ALU environment.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

/*! 
 * Constructor - creates the Alu Environment Configuration object  
 */
 function AluEnvConfig::new(string name = "AluEnvConfig");
   super.new(name);
 endfunction: new