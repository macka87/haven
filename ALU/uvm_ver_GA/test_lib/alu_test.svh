/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_test.svh
 * Description:  UVM Test for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

/*!
 * \brief AluTest
 * 
 * This class represents UVM test for ALU.
 */
 
 class AluTest extends AluTestBase;
    
   //! UVM Factory Registration Macro
   `uvm_component_utils(AluTest)

   /*! 
   * Component Members
   */ 
   TransactionSequence trans_seq;  // sequence of transactions

   /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "AluTest", uvm_component parent = null);
   extern function void build_phase(uvm_phase phase);
   // Other methods
   extern task main_phase(uvm_phase phase);

 endclass: AluTest
 
 
 
/*! 
 * Constructor - creates the AluTest object  
 */
 function AluTest::new(string name = "AluTest", uvm_component parent = null);
   super.new(name, parent);
 endfunction: new



/*! 
 * Build - test configuration
 */ 
 function void AluTest::build_phase(uvm_phase phase);
   super.build_phase(phase);
   
   trans_seq = TransactionSequence::type_id::create("trans_seq");
 endfunction: build_phase



/*! 
 * Main - Stimuli are generated and applied to the DUT
 */     
 task AluTest::main_phase(uvm_phase phase);
    phase.raise_objection(this); 
    
    trans_seq.start(alu_env.alu_agent.trans_sequencer); 
    
    phase.drop_objection(this); 
 endtask: main_phase 