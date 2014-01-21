/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU
 * File Name:    alu_env.svh
 * Description:  ALU environment.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         21.1.2014
 * ************************************************************************** */

/*!
 * \brief AluEnv
 * 
 * This class represents the ALU environment.
 */
 
 class AluEnv;
    
  /*! 
   * Data Members
   */ 
   
   //AluEnvConfig   alu_env_cfg;
   
   // Object for the coverage storage
   //AluCoverageInfo cov_info; 
   
  /*
   * Virtual interfaces
   */    
   virtual iAluIn  dut_alu_in_if;  // ALU input interface
   virtual iAluOut dut_alu_out_if; // ALU output interface  
   
  /*! 
   * Component Members
   */  
   
   AluAgent               alu_agent;
   /*AluScoreboard          alu_scoreboard;
   AluInCoverageMonitor   alu_in_cov_monitor;
   AluOutCoverageMonitor  alu_out_cov_monitor; */
   
   
  /*!
   * Methods
   */
   
   
   // User-defined methods
   extern function new(virtual iAluIn dut_alu_in_if, virtual iAluOut dut_alu_out_if);
   extern function void create_structure();
   extern task run();
   
 endclass: AluEnv


 function AluEnv::new(virtual iAluIn  dut_alu_in_if,
                      virtual iAluOut dut_alu_out_if
                      );
   this.dut_alu_in_if = dut_alu_in_if;  //! Store pointer interface 
   this.dut_alu_out_if = dut_alu_out_if;  //! Store pointer interface  
 endfunction: new  
 

/*! 
 * Constructor - create and configure
 */
 function void AluEnv::create_structure();
   alu_agent = new(dut_alu_in_if, dut_alu_out_if);
 endfunction: create_structure
 
 
/*! 
 * Main run 
 */     
 task AluEnv::run();
   // create agent
   create_structure();
   
   $write("\n\n########## ALU_ENV ##########\n\n");
   
   // run agent
   alu_agent.run();
 endtask: run   
 

 
 /*! 
 * Build - environment configuration
 */ 
 /*function void AluEnv::build_phase(uvm_phase phase);
   // check configuration for the Env
   if (!uvm_config_db #(AluEnvConfig)::get(this, "", "AluEnvConfig", alu_env_cfg)) 
     `uvm_error("MYERR", "AluEnvConfig doesn't exist!"); 
   
   alu_agent = AluAgent::type_id::create("alu_agent", this);
   
   if (alu_env_cfg.has_alu_scoreboard)
     alu_scoreboard = AluScoreboard::type_id::create("alu_scoreboard", this);
     
   if (alu_env_cfg.has_functional_coverage) begin 
     // create object for coverage info
     cov_info = AluCoverageInfo::type_id::create("cov_info");
   
     // set coverage info into the configuration object
     uvm_config_db #(AluCoverageInfo)::set(null, "*", "AluCoverageInfo", cov_info);
   
     alu_in_cov_monitor = AluInCoverageMonitor::type_id::create("alu_in_cov_monitor", this); 
     alu_out_cov_monitor = AluOutCoverageMonitor::type_id::create("alu_out_cov_monitor", this); 
   end  
 endfunction: build_phase */
 
 
 
 /*! 
 * Connect - interconnection of environment components
 */ 
 /*function void AluEnv::connect_phase(uvm_phase phase);
    if (alu_env_cfg.has_alu_scoreboard) begin
      // transactions broadcasts to scoreboard and coverage monitors 
      alu_agent.ap_in.connect(alu_scoreboard.export_alu_in_if);
      alu_agent.ap_out.connect(alu_scoreboard.export_alu_out_if);
      alu_agent.ap_in.connect(alu_in_cov_monitor.analysis_export);
      alu_agent.ap_out.connect(alu_out_cov_monitor.analysis_export);
    end
 endfunction: connect_phase*/ 