/* *****************************************************************************
 * Project Name: Random Search for ALU
 * File Name:    alu_rs_agent.svh
 * Description:  ALU RS Agent.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         17.6.2014
 * ************************************************************************** */

/*!
 * \brief AluRSAgent
 * 
 * This class represents the ALU RS agent.
 */
 
 class AluRSAgent;
    
  /*! 
   * Data Members
   */ 
   AluCoverageInfo cov_info;
         
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
   mailbox #(AluCoverageInfo) coverageMbx;  
  
  /*!
   * Component Members
   */  
   
   TransactionRSSequencer  trans_rs_sequencer;
   AluDriver               alu_driver; 
   AluMonitor              alu_monitor; 
   AluScoreboard           alu_scoreboard;
        
  /*!
   * Methods
   */
   
   // User-defined
   extern function new(virtual iAluIn dut_alu_in_if, virtual iAluOut dut_alu_out_if);
   extern function void create_structure();
   extern task run();
 endclass: AluRSAgent



/*! 
 *  Constructor
 */
 function AluRSAgent::new(virtual iAluIn  dut_alu_in_if,
                          virtual iAluOut dut_alu_out_if
                          );
   this.dut_alu_in_if = dut_alu_in_if;    //! Store pointer interface 
   this.dut_alu_out_if = dut_alu_out_if;  //! Store pointer interface 
 endfunction: new  



/*! 
 * Create and configure environment
 */ 
 function void AluRSAgent::create_structure();
   // >>>>> CREATE COMPONENTS >>>>>
   inputMbx  = new(1);
   sbInMbx   = new(1);
   outputMbx = new(1);
     
   trans_rs_sequencer  = new();
   alu_driver          = new(dut_alu_in_if, TRANS_COUNT); 
   alu_monitor         = new(dut_alu_out_if);
   alu_scoreboard      = new(TRANS_COUNT);
   
   trans_rs_sequencer.inputMbx      = inputMbx;
   alu_driver.sbInMbx               = sbInMbx;
   alu_driver.inputMbx              = inputMbx;
   alu_driver.coverageMbx           = coverageMbx;
   alu_monitor.outputMbx            = outputMbx;
   
   alu_scoreboard.sbInMbx  = sbInMbx; 
   alu_scoreboard.sbOutMbx =  outputMbx; 
 endfunction: create_structure



/*! 
 * Main run
 */ 
 task AluRSAgent::run();
   // create agent objects
   create_structure();
   
   $write("\n\n########## ALU_RS_AGENT ##########\n\n");
   
   fork 
     // run transaction RS sequencer
     trans_rs_sequencer.run();
   
     // run driver
     alu_driver.run();
     
     // run monitor
     alu_monitor.run();
     
     // run scoreboard
     alu_scoreboard.run();
     
   join_any;
   
   // ends all running processes
   disable fork; 
 endtask: run
