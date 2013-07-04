/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_agent_config.svh
 * Description:  Configuration object for the ALU agent.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

/*!
 * \brief AluAgentConfig
 * 
 * This class represents the configuration object for the ALU environment.
 */
 
 class AluAgentConfig extends uvm_object;
    
   //! UVM Factory Registration Macro
   `uvm_object_utils(AluAgentConfig)
   
   //! Virtual interfaces for DUT
   virtual iAluIn  dut_alu_in_if;
   virtual iAluOut dut_alu_out_if;
   
  /*! 
   * Data Members
   */  
   
   uvm_active_passive_enum active = UVM_ACTIVE;
   bit has_functional_coverage    = 0;
   bit has_scoreboard             = 0;
   int trans_count                = 10;
   int populationSize             = 10;
   
  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "AluAgentConfig");
   
 endclass: AluAgentConfig