/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_agent.sv
 * Description:  ALU Agent.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

/*! 
 * Constructor - creates the AluAgent object  
 */
 function AluAgent::new(string name = "AluAgent", uvm_component parent = null);
   super.new(name, parent);
 endfunction: new



/*! 
 * Build - environment configuration
 */ 
 function void AluAgent::build_phase(uvm_phase phase);
   
   // check configuration for the Agent
   if (!uvm_config_db #(AluAgentConfig)::get(this, "", "AluAgentConfig", alu_agent_cfg)) 
     `uvm_error("MYERR", "AluAgentConfig doesn't exist!"); 
     
 endfunction: build_phase



/*! 
 * Connect - interconnection of Agent components.
 */  
 function void AluAgent::connect_phase(uvm_phase phase);
 endfunction: connect_phase
