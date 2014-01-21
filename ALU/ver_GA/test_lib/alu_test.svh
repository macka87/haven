/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU 
 * File Name:    alu_test_base.svh
 * Description:  Test Base Class for ALU - General Test Specification.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         21.1.2014 
 * ************************************************************************** */

/*!
 * \brief AluTest
 * 
 * This class represents the general test specification for ALU.
 */
 class AluTest;  
    
  /*!
   * Component Members
   */
   
   AluEnv          alu_env;        // The environment class
   
  /*
   * Virtual interfaces
   */    
   iAluIn  dut_alu_in_if   (CLK, RST);  // ALU input interface
   iAluOut dut_alu_out_if  (CLK, RST);  // ALU output interface 
  
  
  /*!
   * Data Members
   */
   
   //AluEnvConfig    alu_env_cfg;    // Configuration objects
   //AluAgentConfig  alu_agent_cfg;   

  /*!
   * Methods
   */
   
   // User-defined methods
   extern function void create_structure();
   extern task run();
   //extern function void configure_env(AluEnvConfig cfg);
   //extern function void configure_alu_agent(AluAgentConfig cfg);
 endclass: AluTest
 

 function void new (virtual iAluIn  dut_alu_in_if,
                   virtual iAluOut dut_alu_out_if
                  );
   this.dut_alu_in_if = dut_alu_in_if;  //! Store pointer interface 
   this.dut_alu_out_if = dut_alu_out_if;  //! Store pointer interface  
 endfunction: new  
 
/*! 
 *  Constructor - create and configure environment
 */ 
 function void AluTest::create_structure();
 
   // CONFIGURATION 
   
   // create configuration object for the ALU environment 
   //alu_env_cfg = new();
   
   // configure the ALU environment
   //configure_env(alu_env_cfg);
   
   // create configuration object for the ALU agent
   //alu_agent_cfg = AluAgentConfig::type_id::create("alu_agent_cfg");
   
   // configure the ALU agent using the agent configuration object
   //configure_alu_agent(alu_agent_cfg);
   
   // CREATE THE ALU VERIFICATION ENVIRONMENT
   alu_env = new();
   
 endfunction: create_structure 
 
 
 
/*! 
 * Main run
 */     
 task AluTest::run();
   // ------------------------------------------------------------------------
   $write("\n\n########## NORMAL TEST ##########\n\n");
   
   // create environment 
   create_structure(); 
    
   // run environment
   alu_env.run(); 
 endtask: run  



/*! 
 * Configure the ALU verification environment.
 */  
 /*function void AluTest::configure_env(AluEnvConfig cfg);
   cfg.has_functional_coverage = HAS_FUNCTIONAL_COVERAGE;
   cfg.has_alu_scoreboard      = HAS_ALU_SCOREBOARD;
 endfunction: configure_env*/ 


 
/*! 
 * Configure the ALU agent.
 */  
 /*function void AluTest::configure_alu_agent(AluAgentConfig cfg);
   cfg.active                  = UVM_ACTIVE;
   cfg.has_functional_coverage = HAS_FUNCTIONAL_COVERAGE;
   cfg.has_scoreboard          = HAS_ALU_SCOREBOARD;
   cfg.trans_count             = TRANS_COUNT;
   cfg.trans_count_per_chrom   = TRANS_COUNT_PER_CHROM;
   cfg.populationSize          = POPULATION_SIZE;
 endfunction: configure_alu_agent */