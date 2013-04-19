/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_env.svh
 * Description:  ALU environment.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

/*!
 * \brief AluEnv
 * 
 * This class represents the ALU environment.
 */
 
 class AluEnv extends uvm_env;
    
   //! UVM Factory Registration Macro
   `uvm_component_utils(AluEnv)
   
  /*! 
   * Data Members
   */  
   
   AluAgent                alu_agent;
   AluEnvConfig            alu_env_cfg;
   //AluFuncCoverageMonitor  alu_func_cov_monitor;
   //AluScoreboard           alu_scoreboard;
   
  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "AluEnv", uvm_component parent = null);
   extern function void build_phase(uvm_phase phase);
   extern function void connect_phase(uvm_phase phase);
   
 endclass: AluEnv