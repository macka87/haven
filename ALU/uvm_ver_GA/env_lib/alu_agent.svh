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
   //AluMonitor            alu_monitor; 
   
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



/*! 
 * Constructor - creates the AluAgent object  
 */
 function AluAgent::new(string name = "AluAgent", uvm_component parent = null);
   super.new(name, parent);
 endfunction: new



/*! 
 * Build - environment configuration
 */ 
 function void AluAgent::build_phase(uvm_phase phase);
   // check configuration for the Agent
   if (!uvm_config_db #(AluAgentConfig)::get(this, "", "AluAgentConfig", alu_agent_cfg)) 
     `uvm_error("MYERR", "AluAgentConfig doesn't exist!"); 
     
   // create configuration object for Transaction Sequence
   transaction_sequence_cfg = TransactionSequenceConfig::type_id::create("transaction_sequence_cfg");
   
   // configure transaction sequence
   configure_transaction_sequence(transaction_sequence_cfg);
   
   // put configuration into the configuration space
   uvm_config_db #(TransactionSequenceConfig)::set(this, "*", "TransactionSequenceConfig", transaction_sequence_cfg);  
     
   // >>>>> CREATE COMPONENTS >>>>>
   trans_sequencer = TransactionSequencer::type_id::create("TransactionSequencer", this);
   alu_driver = AluDriver::type_id::create("AluDriver", this); 
   //alu_monitor = AluMonitor::type_id::create("AluMonitor", this);
 endfunction: build_phase



/*! 
 * Connect - interconnection of Agent components.
 */  
 function void AluAgent::connect_phase(uvm_phase phase);
   // TLM connection
   alu_driver.seq_item_port.connect(trans_sequencer.seq_item_export);
 endfunction: connect_phase
 

 
/*! 
 * end_of_elaboration_phase
 */  
 function void AluAgent::end_of_elaboration_phase(uvm_phase phase);
   // TLM connection
   //alu_driver.seq_item_port.debug_connected_to();
 endfunction: end_of_elaboration_phase
 
 

/*! 
 * Configure Transaction Sequence.
 */   
 function void AluAgent::configure_transaction_sequence(TransactionSequenceConfig transaction_sequence_cfg);
   transaction_sequence_cfg.trans_count     = alu_agent_cfg.trans_count;
   transaction_sequence_cfg.populationSize  = alu_agent_cfg.populationSize;    // Size of a population
 endfunction: configure_transaction_sequence