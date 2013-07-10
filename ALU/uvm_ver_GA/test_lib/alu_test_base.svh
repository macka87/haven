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
   * Component Members
   */
   
   AluEnv          alu_env;        // The environment class
  
  /*!
   * Data Members
   */
   
   AluEnvConfig    alu_env_cfg;    // Configuration objects
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
 
 
 
/*! 
 * Constructor - creates the AluTestBase object  
 */
 function AluTestBase::new(string name = "AluTestBase", uvm_component parent = null);
   super.new(name, parent);
 endfunction: new



/*! 
 * Build - environment configuration
 */ 
 function void AluTestBase::build_phase(uvm_phase phase);
    
   // CONFIGURATION 
    
   // create configuration object for the ALU environment 
   alu_env_cfg = AluEnvConfig::type_id::create("alu_env_cfg");
   
   // configure the ALU environment
   configure_env(alu_env_cfg);
   
   // create configuration object for the ALU agent
   alu_agent_cfg = AluAgentConfig::type_id::create("alu_agent_cfg");
   
   // configure the ALU agent using the agent configuration object
   configure_alu_agent(alu_agent_cfg);
   
   // check virtual interfaces of the ALU agent 
   if (!uvm_config_db #(virtual iAluIn)::get(this, "", "AluIn_vif", alu_agent_cfg.dut_alu_in_if)) 
     `uvm_error("MYERR", "iAluIn:dut_alu_in_if interface doesn't exist!");
   if (!uvm_config_db #(virtual iAluOut)::get(this, "", "AluOut_vif", alu_agent_cfg.dut_alu_out_if)) 
     `uvm_error("MYERR", "iAluOut:dut_alu_out_if interface doesn't exist!"); 
     
   // the ALU agent configuration is saved in the configuration object of the 
   // ALU environment
   uvm_config_db #(AluAgentConfig)::set(this, "*", "AluAgentConfig", alu_agent_cfg);  
   
   // CREATE THE ALU VERIFICATION ENVIRONMENT
   alu_env = AluEnv::type_id::create("alu_env", this);
   
 endfunction: build_phase



/*! 
 * Configure the ALU verification environment.
 */  
 function void AluTestBase::configure_env(AluEnvConfig cfg);
   cfg.has_functional_coverage = HAS_FUNCTIONAL_COVERAGE;
   cfg.has_alu_scoreboard      = HAS_ALU_SCOREBOARD;
 endfunction: configure_env


 
/*! 
 * Configure the ALU agent.
 */  
 function void AluTestBase::configure_alu_agent(AluAgentConfig cfg);
   cfg.active                  = UVM_ACTIVE;
   cfg.has_functional_coverage = HAS_FUNCTIONAL_COVERAGE;
   cfg.has_scoreboard          = HAS_ALU_SCOREBOARD;
   cfg.trans_count             = TRANS_COUNT_PER_CHROM;
   cfg.populationSize          = POPULATION_SIZE;
 endfunction: configure_alu_agent 