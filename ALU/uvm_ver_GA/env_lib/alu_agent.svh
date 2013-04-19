/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_agent.svh
 * Description:  ALU Agent.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

/*!
 * \brief AluAgent
 * 
 * This class represents the ALU agent.
 */
 
 class AluAgent extends uvm_component;
    
   //! UVM Factory Registration Macro
   `uvm_component_utils(AluAgent)
   
  /*! 
   * Data Members
   */  
   
   AluAgentConfig  alu_agent_cfg; 
   
  /*!
   * Component Members
   */  
   
   // uvm_analysis_port #(alu_seq_item) ap;
   // budu nasledovat dalsie komponenty  
   
  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "AluAgent", uvm_component parent = null);
   extern function void build_phase(uvm_phase phase);
   extern function void connect_phase(uvm_phase phase);
   
 endclass: AluAgent