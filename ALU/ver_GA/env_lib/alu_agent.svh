/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU
 * File Name:    alu_agent.svh
 * Description:  ALU Agent.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         21.1.2014
 * ************************************************************************** */

/*!
 * \brief AluAgent
 * 
 * This class represents the ALU agent.
 */
 
 class AluAgent;
    
  /*! 
   * Data Members
   */ 
   
  
  /*! 
   * Channels
   */  
   mailbox #(AluInputTransaction) inputMbx; 
   
  
  /*!
   * Component Members
   */  
   
   TransactionSequencer  trans_sequencer;
   AluDriver             alu_driver; 
   AluMonitor            alu_monitor; 
   
  /*!
   * Methods
   */
   
   // User-defined
   extern function void create_structure();
   extern task run();
 endclass: AluAgent



/*! 
 * Constructor - create and configure environment
 */ 
 function void AluAgent::create_structure();
   // >>>>> CREATE COMPONENTS >>>>>
   inputMbx = new();
  
   trans_sequencer = new();
   trans_sequencer.inputMbx = inputMbx;
   
   alu_driver = new(); 
   alu_driver.inputMbx = inputMbx;
   
   alu_monitor = new();
 endfunction: create_structure

/*! 
 * Main run
 */ 
 task AluAgent::run();
   // create agent objects
   create_structure();
   
    $write("\n\n########## ALU_AGENT ##########\n\n");
   
   // run transaction sequencer
   trans_sequencer.run();
   
   // run driver
   alu_driver.run();
 endtask: run  
 
  

