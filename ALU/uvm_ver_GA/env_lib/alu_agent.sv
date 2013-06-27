/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_agent.sv
 * Description:  ALU Agent.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

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
     
   // create components
   trans_sequencer = TransactionSequencer::type_id::create("TransactionSequencer", this);
   alu_driver = AluDriver::type_id::create("AluDriver", this); 
    
 endfunction: build_phase



/*! 
 * Connect - interconnection of Agent components.
 */  
 function void AluAgent::connect_phase(uvm_phase phase);
   alu_driver.seq_item_port.connect(trans_sequencer.seq_item_export); 
 endfunction: connect_phase
 
 

/*! 
 * Configure Transaction Sequence.
 */   
 function void AluAgent::configure_transaction_sequence(TransactionSequenceConfig transaction_sequence_cfg);
   transaction_sequence_cfg.trans_count = alu_agent_cfg.trans_count;
 endfunction: configure_transaction_sequence