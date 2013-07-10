/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_env_config.svh
 * Description:  Configuration object for the ALU environment.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

/*!
 * \brief AluEnvConfig
 * 
 * This class represents the configuration object for the ALU environment.
 */
 
 class AluEnvConfig extends uvm_object;
    
   //! UVM Factory Registration Macro
   `uvm_object_utils(AluEnvConfig)
   
  /*! 
   * Data Members
   */  
   
   bit has_functional_coverage = 1;
   bit has_alu_scoreboard      = 1;
   AluAgentConfig  alu_agent_cfg;   // configuration for subcomponents    
  
  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "AluEnvConfig");
   
 endclass: AluEnvConfig
 
 
 
/*! 
 * Constructor - creates the Alu Environment Configuration object  
 */
 function AluEnvConfig::new(string name = "AluEnvConfig");
   super.new(name);
 endfunction: new 