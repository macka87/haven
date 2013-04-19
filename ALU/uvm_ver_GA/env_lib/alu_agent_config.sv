/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_agent_config.sv
 * Description:  Configuration object for the ALU agent.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

/*! 
 * Constructor - creates the AluAgentConfig object  
 */
 function AluAgentConfig::new(string name = "AluAgentConfig");
   super.new(name);
 endfunction: new