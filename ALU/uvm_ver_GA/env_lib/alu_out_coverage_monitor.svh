                                                                                                                                    /* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_out_coverage_monitor.sv
 * Description:  UVM subscriber for ALU Output Interface 
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         1.8.2013
 * ************************************************************************** */

/*!
 * \brief AluOutCoverageMonitor
 * 
 * Functional Coverage for ALU Output Interface
 * This class measures exercised combinations of interface signals.
 */

 class AluOutCoverageMonitor extends uvm_subscriber #(AluOutputTransaction);
  
  //! UVM Factory Registration Macro
   `uvm_component_utils(AluOutCoverageMonitor)

  /*!
   * Data Members
   */  
   
   // Sampled transaction
   AluOutputTransaction alu_out_trans;
   
   int pkt_cnt;
   
   // Configuration object for the coverage storage
   AluCoverageInfo cov_info;   
   
  /*
   * Definition of covergroups
   */
   
   covergroup alu_out_covergroup;
    
     alu_output_00_FF: coverpoint alu_out_trans.ex_alu {
       bins zeros = {0};
       bins ones  = {8'hFF}; 
     } 
     
   endgroup
   
  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "AluOutCoverageMonitor", uvm_component parent = null);
   extern function void write(AluOutputTransaction t); 
   
 endclass: AluOutCoverageMonitor



/*! 
 * Constructor - creates the AluOutCoverageMonitor object  
 */
 function AluOutCoverageMonitor::new(string name = "AluOutCoverageMonitor", uvm_component parent = null);
   super.new(name, parent);
   alu_out_covergroup = new();
   pkt_cnt = 0;
 endfunction: new 



/*
 * Write - samples values on the interface.  
 */
 function void AluOutCoverageMonitor::write(AluOutputTransaction t);
   
   // get configuration object from database
   if (!uvm_config_db #(AluCoverageInfo)::get(this, "", "AluCoverageInfo", cov_info)) 
     `uvm_error("MYERR", "AluCoverageInfo doesn't exist!"); 
     
   alu_out_trans = t;
   pkt_cnt++;
     
   // sample coverage
   alu_out_covergroup.sample();
   
   cov_info.alu_out_coverage = alu_out_covergroup.get_inst_coverage();  
   //cov_info.alu_out_coverage = $get_coverage();
        
   // print statistics
   uvm_report_info("ALU OUTPUT COVERAGE", $psprintf("%0d Packets sampled, Coverage = %f%% ", pkt_cnt, cov_info.alu_out_coverage));
   
   // store new coverage info into the configuration object
   uvm_config_db #(AluCoverageInfo)::set(this, "*", "AluCoverageInfo", cov_info);
     
 endfunction: write