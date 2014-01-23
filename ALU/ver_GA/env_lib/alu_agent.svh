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
   
  /*
   * Virtual interfaces
   */    
   virtual iAluIn  dut_alu_in_if;  // ALU input interface
   virtual iAluOut dut_alu_out_if; // ALU output interface   
   
  
  /*! 
   * Channels
   */  
   mailbox #(AluInputTransaction) inputMbx; 
   mailbox #(AluInputTransaction) sbInMbx;
   mailbox #(AluOutputTransaction) outputMbx;
   
  
  /*!
   * Component Members
   */  
   
   TransactionSequencer  trans_sequencer;
   AluDriver             alu_driver; 
   AluMonitor            alu_monitor; 
   AluScoreboard         alu_scoreboard;
   
  /*!
   * Methods
   */
   
   // User-defined
   extern function new(virtual iAluIn dut_alu_in_if, virtual iAluOut dut_alu_out_if);
   extern function void create_structure();
   extern task run();
 endclass: AluAgent



/*! 
 *  Constructor
 */
 function AluAgent::new(virtual iAluIn  dut_alu_in_if,
                      virtual iAluOut dut_alu_out_if
                      );
   this.dut_alu_in_if = dut_alu_in_if;    //! Store pointer interface 
   this.dut_alu_out_if = dut_alu_out_if;  //! Store pointer interface  
 endfunction: new  



/*! 
 * Create and configure environment
 */ 
 function void AluAgent::create_structure();
   // >>>>> CREATE COMPONENTS >>>>>
   inputMbx  = new();
   sbInMbx   = new();
   outputMbx = new();
  
   trans_sequencer = new();
   alu_driver = new(dut_alu_in_if); 
   alu_monitor = new(dut_alu_out_if);
   alu_scoreboard = new();
   
   trans_sequencer.inputMbx = inputMbx;
   alu_driver.sbInMbx = sbInMbx;
   alu_driver.inputMbx = inputMbx;
   alu_monitor.outputMbx = outputMbx;
   
   alu_scoreboard.sbInMbx = sbInMbx; 
   alu_scoreboard.sbOutMbx =  outputMbx; 
 endfunction: create_structure



/*! 
 * Main run
 */ 
 task AluAgent::run();
   // create agent objects
   create_structure();
   
   $write("\n\n########## ALU_AGENT ##########\n\n");
   
   fork 
     // run transaction sequencer
     trans_sequencer.run();
   
     // run driver
     alu_driver.run();
     
     // run monitor
     alu_monitor.run();
     
     // run scoreboard
     alu_scoreboard.run();
   join;  
 endtask: run