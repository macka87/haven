/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_test_base.sv
 * Description:  UVM Test Base Class for ALU - General Test Specification.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

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
   alu_env_cfg.alu_agent_cfg = alu_agent_cfg;  
   // da sa to aj inak, konfiguracia alu_agent_cfg bude zasa ulozena do konfig.
   // databazy cez: uvm_config_db #(alu_agent_cfg)::set(this, "*", "alu_agent_cfg", alu_agent_cfg);  
   
   // CREATE THE ALU VERIFICATION ENVIRONMENT
   
   alu_env = AluEnv::type_id::create("alu_env", this);
   
 endfunction: build_phase



/*! 
 * Configure the ALU verification environment.
 */  
 function void AluTestBase::configure_env(AluEnvConfig cfg);
   cfg.has_functional_coverage = 1;
   cfg.has_alu_scoreboard      = 1;
 endfunction: configure_env


 
/*! 
 * Configure the ALU agent.
 */  
 function void AluTestBase::configure_alu_agent(AluAgentConfig cfg);
   cfg.active                  = UVM_ACTIVE;
   cfg.has_functional_coverage = 1;
   cfg.has_scoreboard      = 1;
 endfunction: configure_alu_agent    
 
