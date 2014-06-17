                                            /* *****************************************************************************
 * Project Name: Random Search Algorithm for ALU
 * File Name:    alu_rs_test.svh
 * Description:  RS Test for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         17.6.2014
 * ************************************************************************** */

/*!
 * \brief AluRSTest
 * 
 * This class represents Random Search test for ALU.
 */
 class AluRSTest;  
   
  /*!
   * Component Members
   */
   
   AluRSAgent           alu_rs_agent;          // The agent class
     
  /*
   * Virtual interfaces
   */    
   virtual iAluIn  dut_alu_in_if;  // ALU input interface
   virtual iAluOut dut_alu_out_if; // ALU output interface 
   
  /*! 
   * Channels
   */  
   mailbox #(AluCoverageInfo) coverageMbx;
  
  /*! 
   * Data Members
   */
   AluCoverageInfo cov_info;
        
   /*!
   * Methods
   */
   extern function new(virtual iAluIn dut_alu_in_if, virtual iAluOut dut_alu_out_if);
   extern function void create_structure();
   extern task run();
   
 endclass: AluRSTest
 


/*! 
 *  Constructor
 */
 function AluRSTest::new(virtual iAluIn  dut_alu_in_if,
                         virtual iAluOut dut_alu_out_if
                         );
   this.dut_alu_in_if = dut_alu_in_if;    //! Store pointer interface 
   this.dut_alu_out_if = dut_alu_out_if;  //! Store pointer interface  
  
 endfunction: new   


 
/*! 
 *  Constructor - create and configure environment
 */ 
 function void AluRSTest::create_structure();
   coverageMbx    = new(1);
   
   // CREATE THE ALU VERIFICATION ENVIRONMENT
   alu_rs_agent = new(dut_alu_in_if, dut_alu_out_if);
   
   //chromosome_sequencer.coverageMbx = coverageMbx;
   alu_rs_agent.coverageMbx = coverageMbx;
   
 endfunction: create_structure
 


/*! 
 * Main run
 */     
 task AluRSTest::run();
   process proc;
   	
   // ------------------------------------------------------------------------
   $write("\n\n########## RANDOM SEARCH TEST ##########\n\n");
   
   // create environment 
   create_structure(); 

   proc = process::self();
   proc.srandom(SEED); 
   
   // time measuring
   //$write("START TIME: ");
   //$system("date");
   
   // run environment
   alu_rs_agent.run(); 
   
   // get coverage information
   coverageMbx.get(cov_info);
 
   $write("ALU_IN_COVERAGE: %f%%\n", cov_info.alu_in_coverage);   
 
   // time measuring
   //$write("END TIME: ");
   //$system("date");
   
 endtask: run
