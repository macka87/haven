/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU 
 * File Name:    alu_test_base.svh
 * Description:  Test Base Class for ALU - General Test Specification.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         21.1.2014 
 * ************************************************************************** */

/*!
 * \brief AluTest
 * 
 * This class represents the general test specification for ALU.
 */
 class AluTest;  
    
  /*!
   * Component Members
   */
   
   AluAgent              alu_agent;        // The agent class
      
  /*
   * Virtual interfaces
   */    
   virtual iAluIn  dut_alu_in_if;  // ALU input interface
   virtual iAluOut dut_alu_out_if; // ALU output interface 
  
  /*!
   * Channel
   */
   mailbox #(AluCoverageInfo) coverageMbx;
   
  /*!
   * Data Members
   */     
   AluCoverageInfo cov_info;
   
  /*!
   * Methods
   */
   
   // User-defined methods
   extern function new(virtual iAluIn dut_alu_in_if, virtual iAluOut dut_alu_out_if);
   extern function void create_structure();
   extern task run();
   
 endclass: AluTest



/*! 
 *  Constructor
 */
 function AluTest::new(virtual iAluIn  dut_alu_in_if,
                       virtual iAluOut dut_alu_out_if
                       );
   this.dut_alu_in_if = dut_alu_in_if;    //! Store pointer interface 
   this.dut_alu_out_if = dut_alu_out_if;  //! Store pointer interface  
 endfunction: new  


 
/*! 
 *  Create and configure environment
 */ 
 function void AluTest::create_structure();
   coverageMbx    = new(1);
   
   // CREATE THE ALU VERIFICATION ENVIRONMENT
   alu_agent = new(dut_alu_in_if, dut_alu_out_if);
   
   //chromosome_sequencer.coverageMbx = coverageMbx;
   alu_agent.coverageMbx = coverageMbx;
 endfunction: create_structure 
 
 
 
/*! 
 * Main run
 */     
 task AluTest::run();
 
   // ------------------------------------------------------------------------
   $write("\n\n########## NORMAL TEST ##########\n\n");
   
   // create environment 
   create_structure(); 
   
   // time measuring
   $write("START TIME: ");
   $system("date");
   
   // run environment
   alu_agent.run(); 
   
   // get coverage information
   coverageMbx.get(cov_info);
 
   $write("ALU_IN_COVERAGE: %f%%\n", cov_info.alu_in_coverage);   
 
   // time measuring
   $write("END TIME: ");
   $system("date");
   
 endtask: run
