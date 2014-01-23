/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU
 * File Name:    alu_env.svh
 * Description:  ALU environment.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         21.1.2014
 * ************************************************************************** */

/*!
 * \brief AluEnv
 * 
 * This class represents the ALU environment.
 */
 
 class AluEnv;
    
  /*! 
   * Data Members
   */ 
   
  /*
   * Virtual interfaces
   */    
   virtual iAluIn  dut_alu_in_if;  // ALU input interface
   virtual iAluOut dut_alu_out_if; // ALU output interface  
   
  /*! 
   * Component Members
   */  
   
   AluAgent               alu_agent;
   
   /*AluInCoverageMonitor   alu_in_cov_monitor;
   AluOutCoverageMonitor  alu_out_cov_monitor; */
   
   
  /*!
   * Methods
   */
   
   
   // User-defined methods
   extern function new(virtual iAluIn dut_alu_in_if, virtual iAluOut dut_alu_out_if);
   extern function void create_structure();
   extern task run();
   
 endclass: AluEnv


/*! 
 *  Constructor
 */
 function AluEnv::new(virtual iAluIn  dut_alu_in_if,
                      virtual iAluOut dut_alu_out_if
                      );
   this.dut_alu_in_if = dut_alu_in_if;    //! Store pointer interface 
   this.dut_alu_out_if = dut_alu_out_if;  //! Store pointer interface  
 endfunction: new  
 


/*! 
 * Create and configure
 */
 function void AluEnv::create_structure();
   alu_agent = new(dut_alu_in_if, dut_alu_out_if);
 endfunction: create_structure
 

 
/*! 
 * Main run 
 */     
 task AluEnv::run();
   // create agent
   create_structure();
   
   $write("\n\n########## ALU_ENV ##########\n\n");
   
   // run agent
   alu_agent.run();
 endtask: run 