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
   TransactionSequenceConfig transaction_sequence_cfg;
   
  /*!
   * Component Members
   */  
   
   uvm_analysis_port #(AluInputTransaction) ap;
   
   TransactionSequencer  trans_sequencer;
   AluDriver             alu_driver; 
   
  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "AluAgent", uvm_component parent = null);
   extern function void build_phase(uvm_phase phase);
   extern function void connect_phase(uvm_phase phase);
   extern function void end_of_elaboration_phase(uvm_phase phase);
   
   // Own UVM methods
   extern function void configure_transaction_sequence(TransactionSequenceConfig transaction_sequence_cfg);
   
 endclass: AluAgent