/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_test_base.svh
 * Description:  UVM Test Base Class for ALU - General Test Specification.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

/*!
 * \brief AluTestBase
 * 
 * This class represents the general UVM test specification for ALU.
 */
 
 class AluTestBase extends uvm_test;
    
   //! UVM Factory Registration Macro
   `uvm_component_utils(AluTestBase)
   
  /*! 
   * Data Members
   */  
  
  /*!
   * Component Members
   */
   
   // The environment class
   AluEnv          alu_env;
   
   // Configuration objects
   AluEnvConfig    alu_env_cfg;
   AluAgentConfig  alu_agent_cfg;   

  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "AluTestBase", uvm_component parent = null);
   extern function void build_phase(uvm_phase phase);
   // Other methods
   extern virtual function void configure_env(AluEnvConfig cfg);
   extern virtual function void configure_alu_agent(AluAgentConfig cfg);

 endclass: AluTestBase